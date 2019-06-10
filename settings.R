
# 0. package call ---------------------------------------------------------

# For preprocessing
library(stringr)
library(dplyr)

# For fitting interpretable model
library(glmnet)       # LASSO-penalized GLM
library(mboost)       # Componentwise Gradient Boosting

# For fitting predictive model
library(caret)        # To use confusionMatrix
library(randomForest) # randomForest
library(e1071)        # SVM
library(xgboost)      # XGBoost
library(mgcv)         # Ensemble through GAM

# 1. preprocessing --------------------------------------------------------

logical_match <- function (input_data) {
  cleaned <- input_data
  
  # 1. Revise loan amount to zero
  # Client whose total loan record equals to 0 will have value of 4
  loan_count <- (input_data[, 3] == 0) +
    (input_data[, 4] == 0) +
    (input_data[, 5] == 0) +
    (input_data[, 6] == 0)
  # Revise loan amount of such people to zero
  cleaned[loan_count == 4, 7] <- 0
  cleaned[loan_count == 4, 8] <- 0
  
  # 2. Revise delay ratio to zero
  # Client whose max monthly input equals to 0 will have value of TRUE
  maxinput_zero <- input_data[, 44] == 0
  # Revise their
  cleaned[maxinput_zero, 34] <- 0 # total delay ratio 
  cleaned[maxinput_zero, 35] <- 0 # delay ratio in latest year
  cleaned[maxinput_zero, 40] <- 0 # delay ratio of assurance product
  cleaned[maxinput_zero, 41] <- 0 # delay ratio of depository product
  # to zero
  
  # 3. Revise insurance return to zero
  # Client who doesn't have history of request on insurance return will have value of TRUE
  request_zero <- input_data[, 51] == 0
  cleaned[request_zero, 50] <- 0
  
  return(cleaned)
}


rightmost_cleaner <- function (column) {
  # Replacing trivial '1' at the rightmost letter
  target <- column
  # Replace rightmost letter of element whose rightmost letter is 1 to 0
  str_sub(target[str_sub(target, -1, -1) == 1], -1 , -1) <- 0
  
  return(as.integer(target))
}


scaling_column <- function (input_data) {
  cleaned <- input_data
  
  # Different company used different unit(SCI : 1000, Hanhwa : 10000)
  cleaned <- cleaned %>% 
    mutate_at(c(7:10, 16, 18, 19, 24), rightmost_cleaner) %>% 
    mutate_at(c(7:10, 16), list(~ . * 1000)) %>% 
    mutate_at(c(18, 19, 24), list(~ . * 10000))
  
  return(cleaned)
}


rephrase_date <- function (input_data) {
  cleaned <- input_data
  
  # TEL_CNTT_QTR : YYYY/Q(the year and the quarter that the customer enrolled telecom service)
  # 20162(second quarter of 2016) was the latest. Thus each value should be rephrased to:
  # 20162 -> 0, 20161 -> 1, 20154 -> 2, 20153 -> 3, 20152 -> 4, 20151 -> 5, 20144 -> 6, ...
  #
  # To obtain such mapping, first 20162 is subtracted from each value.
  # Then with its absoulute value, following mapping rule is applied:
  # (1) If first digit is less than 7, save that digit as it is;
  #     if it's over 7, subtract 6 from that digit and save that value.
  # (2) Next, divide that value by 10 and discard the remaining. 
  # (3) Then add (that quotient) * 4 to obtain mapping
  #
  # Ex) map 20144 to 6
  # (1) |20144 - 20162| = 18 (First digit is 8; therefore save 8 - 6 = 2)
  # (2) 18 / 10 = 1.8 -> 1 (discard the remaining)
  # (3) Add 1 * 4 = 4 to the value(i.e. 2 + 4 = 6)
  
  # initialize
  dist_year <- abs(input_data[, 62] - 20162)
  
  # (1)
  first_digit <- as.numeric(str_sub(dist_year, -1, -1))
  first_digit[first_digit > 7] <- first_digit[first_digit > 7] - 6
  
  # (2)
  dist_year <- floor(dist_year / 10)
  
  # Revise data as planned
  cleaned[, 62] <- first_digit + (dist_year * 4)
  
  # MIN_CNTT_DATE : YYYY/MM(year and month that Hanhwa lend the money to the client first time)
  # Same idea can be applied, but 90% of data already has value of 0
  # (i.e. 90% of the customer didn't borrowed money from Hanhwa; 
  # showing the lackness of lending experience toward middle-credit customers)
  
  year <- str_sub(input_data[, 26], 1, 4)
  month <- str_sub(input_data[, 26], 5, 6)
  month[month == ""] <- "0"
  distance <- 12 * (2016 - as.integer(year)) + (6 - as.integer(month))
  distance[distance > 100] <- 0
  cleaned[, 26] <- distance

  
  return(cleaned)
}


trivials <- function (input_data) {
  cleaned <- input_data
  
  # latest_binary
  latest_binary <- rep(1, nrow(input_data))
  latest_binary[input_data[, 22] == 0 | is.null(input_data[, 22])] <- 0
  cleaned[, 22] <- as.factor(latest_binary)
  rm('latest_binary')
  
  # revise interval into numeric value by using its median
  delay_ratio_latest <- input_data[, 35]
  cleaner <- rep(0, nrow(cleaned))
  cleaner[delay_ratio_latest=='10미만'] <- 5
  cleaner[delay_ratio_latest=='20미만'] <- 15
  cleaner[delay_ratio_latest=='30미만'] <- 25
  cleaner[delay_ratio_latest=='40미만'] <- 35
  cleaner[delay_ratio_latest=='50미만'] <- 45
  cleaner[delay_ratio_latest=='60미만'] <- 55
  cleaner[delay_ratio_latest=='90미만'] <- 75
  cleaner[delay_ratio_latest=='90이상'] <- 95
  cleaned[, 35] <- cleaner
  rm('cleaner', 'delay_ratio_latest')
  
  # Making masked value to zero
  age <- as.character(input_data[, 53])
  age[age == '*'] <- 0
  cleaned[, 53] <- as.integer(age)
  rm('age')
  
  return(cleaned)
}



# 1-1. derived variable -----------------------------------------------------


# 1-1-1. By intuition -------------------------------------------------------


add_intuitive <- function (input_data) {
  added <- input_data
  
  # (1) lately_delayed
  lately_delayed <- rep(0, nrow(input_data))
  lately_delayed[input_data$CRMM_OVDU_AMT != 0 | input_data$CRLN_30OVDU_RATE != 0] <- 1
  added$lately_delayed <- as.factor(lately_delayed)
  
  # (2) middle_loan_ratio
  nan_handler <- input_data$TOT_LNIF_AMT == 0
  middle_loan_ratio <- input_data$CPT_LNIF_AMT / input_data$TOT_LNIF_AMT
  middle_loan_ratio[nan_handler] <- 0
  # To eliminate NaN created by division by zero
  added$middle_loan_ratio <- middle_loan_ratio
  
  # (3) amount_per_gurantee
  nan_handler <- input_data$CB_GUIF_CNT == 0
  amount_per_gurantee <- input_data$CB_GUIF_AMT/input_data$CB_GUIF_CNT
  amount_per_gurantee[nan_handler] <- 0
  # To eliminate NaN created by division by zero
  added$amount_per_gurantee <- amount_per_gurantee
  
  # (4) amount_per_bankloan
  nan_handler <- input_data$BNK_LNIF_CNT == 0
  amount_per_bankloan <- input_data$BNK_LNIF_AMT / input_data$BNK_LNIF_CNT
  amount_per_bankloan[nan_handler] <- 0
  # To eliminate NaN created by division by zero
  added$amount_per_bankloan <- amount_per_bankloan
  
  return(added)
}


# 1-1-2. By Chi-square partition --------------------------------------------

revalue_column_conttable <- function (input_data, target, nlevels_groupA) {
  if (is.character(target)) {
    target_index <- which(names(input_data) == target)
  } else {
    target_index <- target
  } # whether target is index of variable or variable's name, 
    # target_index will always contain index of the variable.
  
  levels_groupA <- levels(factor(input_data[, target_index]))[1:nlevels_groupA]
  # levels_groupA is a set of values that will be encoded as group A.
  revalue_result <- rep("B", nrow(input_data))
  revalue_result[input_data[, target_index] %in% levels_groupA] <- "A"
  # if value of a cell is element of levels_groupA, encode it as 'A'
  
  return(revalue_result)
}

ordinal_signif_conttable <- function (input_data, index) {
  
  index_level <- as.numeric(levels(factor(input_data[, index])))
  seperator <- numeric(length(index_level) - 1)
  chisq <- numeric(length(index_level) - 1)
  
  for(i in 1:(length(index_level) - 1)){
    # (1) Bisect the variable
    grouped <- revalue_column_conttable(input_data, index, i)
    # (2) Build contingency table
    critical_table <- table(input_data$TARGET, grouped)
    # (3) Calculate Chi-square statistic
    a <- as.numeric(critical_table[1, 1])
    b <- as.numeric(critical_table[1, 2])
    c <- as.numeric(critical_table[2, 1])
    d <- as.numeric(critical_table[2, 2])
    n <- sum(critical_table)
    
    seperator[i] <- index_level[i]
    chisq[i] <- n * ((a * d - b * c) ^ 2) / ((a + b) * (c + d) * (a + c) * (b + d))
  }
  
  return(data.frame(sep = seperator, chisquare = chisq))
}

compound_2var <- function(input_data, index1, index2, nlevels_A1, nlevels_A2){
  # 1. Bisect two variables
  revalue1 <- revalue_column_conttable(input_data, index1, nlevels_A1)
  revalue2 <- revalue_column_conttable(input_data, index2, nlevels_A2)
  
  # 2. Label the case into one of four
  # 2-1. Initialize every label to zero
  complected <- rep(0, nrow(input_data))
  # 2-2. Filter the values whose first variable belongs to group B 
  #      and label them as either 0 or 2
  complected[revalue1 == 'B'] <- 2
  # 2-3. Filter the values whose second variable belongs to B and add 1
  #      (then they will be labeled as either 1 or 3;
  #      1 if first = A and second = B, 3 if first = B and second = B)
  #      and replace this value to complete labelling
  complected[revalue2 == 'B'] <- complected[revalue2 == 'B'] + 1
  
  return(complected)
}

compound3456 <- function (input_data) {
  
  # Store bisected result of 4 variables
  subsetted_factored <- as.data.frame(
    cbind(revalue_column_conttable(input_data, 3, 1),
          revalue_column_conttable(input_data, 4, 1),
          revalue_column_conttable(input_data, 5, 2),
          revalue_column_conttable(input_data, 6, 2))
  )
  
  # Label 16 different cases 
  # ; using the same labeling technique in compound_2var function
  category_3456 <- rep(0, nrow(subsetted_factored))
  category_3456[subsetted_factored[, 1] == 'B'] <- category_3456[subsetted_factored[, 1] == 'B'] + 1
  category_3456[subsetted_factored[, 2] == 'B'] <- category_3456[subsetted_factored[, 2] == 'B'] + 2
  category_3456[subsetted_factored[, 3] == 'B'] <- category_3456[subsetted_factored[, 3] == 'B'] + 4
  category_3456[subsetted_factored[, 4] == 'B'] <- category_3456[subsetted_factored[, 4] == 'B'] + 8
  
  # compound some features
  # ; as in phonefee_delaytrend making procedure
  category_3456[category_3456 == 0] <- 'A'
  category_3456[category_3456 == 1] <- 'A'
  category_3456[category_3456 == 2] <- 'B'
  category_3456[category_3456 == 3] <- 'A'
  category_3456[category_3456 == 4] <- 'B'
  category_3456[category_3456 == 5] <- 'B'
  category_3456[category_3456 == 6] <- 'B'
  category_3456[category_3456 == 7] <- 'B'
  category_3456[category_3456 == 8] <- 'C'
  category_3456[category_3456 == 9] <- 'B'
  category_3456[category_3456 == 10] <- 'B'
  category_3456[category_3456 == 11] <- 'B'
  category_3456[category_3456 == 12] <- 'C'
  category_3456[category_3456 == 13] <- 'C'
  category_3456[category_3456 == 14] <- 'C'
  category_3456[category_3456 == 15] <- 'C'
  
  return(category_3456)
}

add_chisquare <- function (input_data) {
  loaner_effect1 <- compound3456(input_data)
  
  credit_effect <- compound_2var(input_data, 7, 9, 8, 5)
  credit_effect[credit_effect == 0] <- 'A'
  credit_effect[credit_effect == 1] <- 'B'
  credit_effect[credit_effect == 2] <- 'C'
  credit_effect[credit_effect == 3] <- 'D'
  
  loaner_effect2 <- compound_2var(input_data, 11, 12, 2, 2)
  loaner_effect2[loaner_effect2 == 0] <- 'A'
  loaner_effect2[loaner_effect2 == 1] <- 'B'
  loaner_effect2[loaner_effect2 == 2] <- 'C'
  loaner_effect2[loaner_effect2 == 3] <- 'D'
  
  periodic_failure <- compound_2var(input_data, 49, 52, 1, 1)
  periodic_failure[periodic_failure == 1] <- 'A'
  periodic_failure[periodic_failure == 0] <- 'B'
  periodic_failure[periodic_failure == 3] <- 'C'
  periodic_failure[periodic_failure == 2] <- 'D'
  
  phonefee_delaytrend <- compound_2var(input_data, 64, 66, 3, 4)
  phonefee_delaytrend[phonefee_delaytrend == 0] <- 'A'
  phonefee_delaytrend[phonefee_delaytrend == 1 | phonefee_delaytrend == 2] <- 'B'
  phonefee_delaytrend[phonefee_delaytrend == 3] <- 'C'
  
  # Add generated variables
  added <- input_data
  added$loaner_effect1 <- as.factor(loaner_effect1)
  added$credit_effect <- as.factor(credit_effect)
  added$loaner_effect2 <- as.factor(loaner_effect2)
  added$periodic_failure <- as.factor(periodic_failure)
  added$phonefee_delaytrend <- as.factor(phonefee_delaytrend)
  
  return(added)
}


# 2. Fit interpretable model ----------------------------------------------

# 2-1. Significance of Derived variables ----------------------------------

resampler <- function (input_data, tr_rate) {
  original_data <- input_data
  
  # 1. Save indices of zero and one proportional to the rate of training data(tr_rate)
  # 1-1. index_zero : Randomly select (tr_rate * 100)% of zeros
  index_zero <- sample(which(original_data$TARGET == 0),
                       round(length(which(original_data$TARGET == 0)) * tr_rate, 0),
                       replace = F)
  # 1-2. index_one : Randomly select (tr_rate * 100)% of ones
  index_one <- sample(which(original_data$TARGET == 1),
                      round(length(which(original_data$TARGET == 1)) * tr_rate, 0),
                      replace = F)
  
  # 2. Save training, test data into the global scope
  train_data <<- rbind(original_data[index_zero, ], original_data[index_one, ])
  test_data <<- original_data[-as.numeric(rownames(train_data)), ]
}

find_best_cutoff <- function (testdata, cutoff, fitted_glmnet) {
  # Subroutine for finding best cutoff point
  
  # 1. Obtain a vector of prediction on test data as a probability(type = 'response')
  lambda <- fitted_glmnet$lambda.1se
  predicted <- predict(fitted_glmnet, 
                       model.matrix(CUST_ID + TARGET ~ ., data = testdata),
                       s = lambda,
                       type = 'response')
  
  # 2. Create a vector to store f-measure values
  result <- vector('numeric', length(cutoff))
  
  # 3. Begin recording
  for(i in 1:length(cutoff)){
    # If probability > cutoff, record it as 1
    lasso_result <- rep(0, nrow(testdata))
    lasso_result[predicted >= cutoff[i]] <- 1
    
    # calculate F1 score
    critical_table <- table(true = testdata$TARGET, 
                            pred = lasso_result)
    precision <- critical_table[2, 2] / (critical_table[1, 2] + critical_table[2, 2])
    recall <- critical_table[2, 2] / (critical_table[2, 1] + critical_table[2, 2])
    F1_score <- 2 * precision * recall / (precision + recall)
    
    # record cutoff point and corresponding F1_score
    result <- F1_score
  }
  
  # 4. Return the result
  return(result)
}

performance_tester_LASSO <- function (training, test, coef_return = TRUE) {
  # This function returns the test-F1 score calculated by the best set of estimators for given combination of data. 
  # Optionally returns corresponding selected coefficients.
  #
  # 1. Applying Cross-Validation to find best coefficient estimate
  #
  # Since this is highly unbalanced data, measuring the fit simply by misclassification error
  # (i.e. type.measure = 'class') seemed inappropriate. Therefore, AUC is used as a measure of the fit.
  logistic_fit <- cv.glmnet(model.matrix(CUST_ID + TARGET ~ ., data = training), training$TARGET, 
                            alpha = 1, family = 'binomial', type.measure = 'auc')
  
  # 2. Obtain the list of F1 scores
  if (coef_return) {
    return(list(fmeasure = find_best_cutoff(test, cutoff_points, logistic_fit),
                coef = data.frame(
                  names = rownames(coef(logistic_fit, s = logistic_fit$lambda.1se)),
                  values = as.numeric(coef(logistic_fit, s = logistic_fit$lambda.1se))
                )))
  } else {
    return(fmeasure = find_best_cutoff(test, cutoff_points, logistic_fit))
  }
}


# 2-2. Justification on Boosting method -------------------------------------
performance_tester_Boosting <- function (training, test, coef_return = TRUE) {
  # This function returns the test-F1 score calculated by the best set of estimators for given combination of data. 
  # Optionally returns corresponding selected coefficients.
  #
  # 1. Obtain fitted logistic regression using Componentwise Boosting method
  logistic_fit <- glmboost(TARGET ~ ., 
                           data = training, 
                           family = Binomial(type='glm', link='logit'), 
                           control=boost_control(mstop=10000))
  
  # 2. Obtain the list of F1 scores
  result <- matrix(0, nrow = 2, ncol = length(cutoff_points))
  for (i in 1:length(cutoff_points)) {
    gbtable <- table(data$TARGET,
                     ifelse(predict(gbobject, newdata = test, type='response') > cutoff[i], 1, 0))
    a <- gbtable[2,2] / (gbtable[1, 2] + gbtable[2, 2])
    b <- gbtable[2,2] / (gbtable[2, 1] + gbtable[2, 2])
    result[1, i] <- cutoff[i]
    result[2, i] <- 2 * a * b / (a + b)
  }
  
  highest <- max(result[, 2])
  if (coef_return) {
    return(list(fmeasure = highest,
                cutoff = result[which(result[, 2] == highest), 1],
                coefficient = coef(logistic_fit)
                ))
  } else {
    return(highest)
  }
}


# 3. Fit predictive model -------------------------------------------------

dummy_column_maker <- function (column) {
  # input  : selected column of the data
  # output : dummy-processed result of that column
  level_names <- levels(factor(column))
  nlevel <- length(level_names)
  storage <- matrix(rep(0, length(column) * nlevel), ncol = nlevel)
  
  # Create dummy column for each level
  for (i in 1:nlevel) storage[column == level_names[i], i] <- 1
  
  # Return the result as data frame
  result <- as.data.frame(storage)
  names(result) <- paste0('_', level)
  return(result)
}

dummy_process <- function(input_data, colname){
  colnum <- which(names(input_data) == colname)
  if (colnum == length(input_data)) {
    # If the last variable of the data is factor variable, dummy-process that last column and return it as NewData.
    NewData <- cbind(input_data[, 1:(colnum - 1)], dummy_column_maker(input_data[, colnum]))
  } else {
    NewData <- cbind(input_data[, 1:(colnum - 1)],
                     dummy_column_maker(input_data[,colnum]),
                     input_data[, (colnum + 1):length(input_data)])
  }
  return(NewData)
}

dummy_processed_data = function(data){
  # 1. Store the name of the column whose value is in factor type
  FacCol <- c()
  for (i in 1:length(data)){
    if (class(data[,i]) == 'factor') FacCol <- c(FacCol, names(data)[i])
  }
  
  # 2. Conduct dummy_process to that data
  processed_data <- dummy_process(data, FacCol[1])
  for (i in 2:length(FacCol)) processed_data <- dummy_process(processed_data, FacCol[i])
  return(processed_data)
}

getF1score <- function (cmat = NULL, test = NA, pred = NA) {
  if (is.na(test)) {
    # If entered confusionMatrix(i.e. in case of RF, SVM)
    precision <- cmat$table[2, 2] / (cmat$table[1, 2] + cmat$table[2, 2])
    recall    <- cmat$table[2, 2] / (cmat$table[2, 1] + cmat$table[2, 2])
    f1score   <-  2 * precision * recall / (precision + recall)
    return(f1score)
  } else {
    preds     <- as.numeric(pred > 0.2)
    labels    <- test$TARGET
    precision <- sum(preds == 1 & labels == 1) / sum(labels == 1)
    recall    <- sum(preds == 1 & labels == 1) / sum(preds == 1)
    f1score   <- (2 * precision * recall) / (precision + recall)
    return(f1score)
  }
}