rm(list=ls())
options(warn = -1)
# load necessary libraries
library(survival)
library(rdrobust)
library(rpart)
library(boot)
library(pec)
library(riskRegression)
##############################################################
#### Thank you for Dr. Jon Steingrimsson to provide codes 
#### for outcome regressions
#### These are functions used to compute conditional expectation
##############################################################

coxx <- function(obs,delta,xx){
  # Fitting the Cox model
  # Creating the data frame
  obs.sort <- sort(obs)
  data.fit <- data.frame(obs, delta, xx)
  cox.fit <- coxph(Surv(obs,delta) ~ xx,data=data.fit, x=TRUE)
  cox.fit.surv <- predictSurvProb(cox.fit,newdata = data.fit,times = obs.sort)
  m1=matrix(0,nu, nu)
  surv.diff <- matrix(0, ncol = nu, nrow = nu)
  for(i in 1:nu){
    # Getting the properties of the survival cox function for observation i.
    # Calculating the jumps in the Cox model survival curve estimator
    surv.diff[i, ] <- c(1, cox.fit.surv[i,-length(cox.fit.surv[i,])]) - cox.fit.surv[i,]
  }
  
  for (j in 1:nu)
  {
    if(delta[j]==FALSE){
      
      for(i in 1:nu)
      {
        if(obs[j]<=obs[i]){
          
          if(max(obs[delta==1]) > obs[j]){
            # Calculating the conditional expectation E(log(T)|T > T_j,W_i)
            m1[j,i]= sum(log(obs.sort[obs.sort > obs[j]]) * surv.diff[i,][obs.sort > obs[j]])/sum(surv.diff[i, ][obs.sort > obs[j]])
          }
        }
      }
      if(max(obs[delta==1]) <= obs[j]){
        m1[j,]=log(obs[j])
      }
    }	
  }
  return(m1)
}

estCondFun_lognorm <- function(u){
  # Avoiding running into numerical errors by using E[Z|Z > x] = x if x > 5
  # Check if good approdeltamation
  #u = seq(-10, 10, 0.1); plot(u, dnorm(u)/(1 - pnorm(u))); abline(0,1)
  if(u > 5){
    fun.val = u
  }
  if(u <= 5){
    fun.val = dnorm(u)/(pnorm(u, lower = FALSE))
  }
  
  return(fun.val)
}

estCondFun_loglogistic <- function(u){
  # Avoiding running into numerical errors by using E[Z|Z > x] = x+1 if x > 15
  # Check if good approximation
  # u = seq(-10, 10, 0.1); plot(u, u + (log(1 + exp(u)) - u) * (1 + exp(u))); abline(1,1) 
  if(u > 15){
    fun.val = u + 1
  }
  if(u <= 15){
    fun.val = u + (log(1 + exp(u)) - u) * (1 + exp(u))
  }
  return(fun.val)
}


aftlognorm <- function(obs,delta,xx){
  aft.fit <- survreg(Surv(obs, delta) ~ xx, dist = "lognorm")
  m1 = matrix(0,ncol=nu,nrow=nu)
  beta.fit <- aft.fit$coefficients
  scale.fit <- aft.fit$scale
  for(j in 1:nu){
    if(delta[j]==FALSE){
      for(i in 1:nu){
        res.fit <- (log(obs[j]) - beta.fit[1] - beta.fit[-1] * xx[i])/scale.fit
        m1[j,i]<- beta.fit[1] + beta.fit[-1] * xx[i] + scale.fit*estCondFun_lognorm(res.fit)  
      }
    }
  }
  return(m1)
}

aftloglogistic <- function(obs,delta,xx){
  aft.fit <- survreg(Surv(obs,delta) ~ xx, dist = "loglogistic")
  m1 = matrix(0,ncol=nu,nrow=nu)
  beta.fit <- aft.fit$coefficients
  scale.fit <- aft.fit$scale
  for(j in 1:nu){
    if(delta[j]==FALSE){
      for(i in 1:nu){
        res.fit <- (log(obs[j]) - beta.fit[1] - beta.fit[-1] * xx[i])/scale.fit
        m1[j,i]<- beta.fit[1] + beta.fit[-1] * xx[i] + scale.fit*estCondFun_loglogistic(res.fit)  
      }
    }
  }
  return(m1)
}
###############################   END OF COND EXP CALCULATION

##############################################################
# Estimation of censoring distribution
# Changing the dataset to account for truncation. 
# 5% truncation, guarantee positive probability for censoring distribution
##############################################################

Gfunc=function(obs,delta)
{
  delta[order(obs)][floor(nu-0.05*nu):nu]=TRUE
  
  #Calculating the hazard estimator. 
  hazC=mapply(function(xx,dd){dd/sum((obs>=xx))},xx=obs,dd=1-delta)
  surC_km=mapply(function(xx){prod(1-hazC[obs<=xx])},xx=obs)
  return(list(surC_km,obs,delta))	
}

mfunc <- function(obs,delta,xx,mtype){
  if(mtype=="cox"){
    m1 <- coxx(obs,delta,xx)
  }
  if(mtype=="lognorm"){
    m1 <- aftlognorm(obs,delta,xx)
  }
  if(mtype=="loglogistic"){
    m1 <- aftloglogistic(obs,delta,xx)
  }
  return(m1)
}
##############################################################
# EXTERNAL_DR calculates the items that will be needed to compute the
# transformations. 
# Inputs: obs = observed time, delta = failure indicator, xx: covariates
##############################################################

external_DR=function(obs,delta,xx,mtype)
{
  # Calculating the conditional expectation   
  m1 <- mfunc(obs,delta,xx,mtype)
  
  # Calculating the conditional censoring distribution.
  tem=Gfunc(obs,delta)
  # Calculating the censoring distribution
  surC_km=tem[[1]]
  # Observed event times for adjusted for truncation
  obs=tem[[2]]
  # Failure indicator adjusted for truncation
  delta=tem[[3]]
  
  # Calculating a0, a1, b0, b1, c0, c1
  a0=delta/surC_km
  a1=a0*log(obs)

  b0=(1-delta)/surC_km
  b1=b0*diag(m1)

  kk=mapply(function(tt){sum((tt<=obs))},tt=obs)
  c0=mapply(function(tt){sum(b0*(obs<=tt)/kk)},tt=obs)
  c1=mapply(function(tt,i){sum(b0*(obs<=tt)*m1[,i]/kk)},tt=obs,i=1:nu)

  parms = c(a0,a1,b0,b1,c0,c1)
  
  return(parms)
}

# data generation
gen.data <- function(seednum,beta10,beta20,beta30){
  set.seed(seednum)
  W <- runif(nu,0,1)
  eps <- rnorm(nu,0,0.25)
  Time <- exp(beta10 + beta20*W + beta30 * as.numeric(W >= 0.5) + eps)		
  Cen <- runif(nu,0,50)
  return(list(Time,Cen,W))
}

nu <- 200 # sample size
seednum <- 1
dat <- gen.data(seednum=seednum,beta10=2,beta20=1,beta30=1)
Time <- dat[[1]]
Cen <- dat[[2]]
W <- dat[[3]]
y <- pmin(Time,Cen)
status <- as.numeric(Time <= Cen)
cen.rate <- 1-sum(status)/nu

# calculation of external parameters 
beta30 <- 1
#values_km_DR <- external_DR(y,status,W,"tree_km")
values_cox_DR <- external_DR(y,status,W,"cox")
values_lognorm_DR <- external_DR(y,status,W,"lognorm")
values_loglogistic_DR <- external_DR(y,status,W,"loglogistic")

# calculation of transformed responses
# IPCW
time_trans_IPCW <- values_cox_DR[(nu+1):(2*nu)] 

# DR
time_trans_cox_DR <- values_cox_DR[(nu+1):(2*nu)] + values_cox_DR[(3*nu+1):(4*nu)] - values_cox_DR[(5*nu+1):(6*nu)]
time_trans_lognorm_DR <- values_lognorm_DR[(nu+1):(2*nu)] + values_lognorm_DR[(3*nu+1):(4*nu)] - values_lognorm_DR[(5*nu+1):(6*nu)]
time_trans_loglogistic_DR <- values_loglogistic_DR[(nu+1):(2*nu)] + values_loglogistic_DR[(3*nu+1):(4*nu)] - values_loglogistic_DR[(5*nu+1):(6*nu)]  

# fit sharp design
# bandwidth : Ludwig and Miller
# vec = nearest neightbor
# IPCW
h_IPCW <- rdbwselect_2014(time_trans_IPCW,W,c=0.5,bwselect="CV")
fit_IPCW_nn <- rdrobust(time_trans_IPCW,W,c=0.5,h=h_IPCW$bws[1],b=h_IPCW$bws[2],vce="nn")
fit_IPCW_hc0 <- rdrobust(time_trans_IPCW,W,c=0.5,h=h_IPCW$bws[1],b=h_IPCW$bws[2],vce="hc0")

# Doubly robust 
# object name with cox : Cox 
# object name with lognorm : lognormal
# object name with loglogistic : log-logistic
h_cox_DR <- rdbwselect_2014(time_trans_cox_DR,W,c=0.5,bwselect = "CV")
fit_cox_DR_nn <- rdrobust(time_trans_cox_DR,W,c=0.5,h=h_cox_DR$bws[1],b=h_cox_DR$bws[2],vce="nn")
fit_cox_DR_hc0 <- rdrobust(time_trans_cox_DR,W,c=0.5,h=h_cox_DR$bws[1],b=h_cox_DR$bws[2],vce="hc0")
h_lognorm_DR <- rdbwselect_2014(time_trans_lognorm_DR,W,c=0.5,bwselect = "CV")
fit_lognorm_DR_nn <- rdrobust(time_trans_lognorm_DR,W,c=0.5,h=h_lognorm_DR$bws[1],b=h_lognorm_DR$bws[2],vce="nn")
fit_lognorm_DR_hc0 <- rdrobust(time_trans_lognorm_DR,W,c=0.5,h=h_lognorm_DR$bws[1],b=h_lognorm_DR$bws[2],vce="hc0")
h_loglogistic_DR <- rdbwselect_2014(time_trans_loglogistic_DR,W,c=0.5,bwselect = "CV")
fit_loglogistic_DR_nn <- rdrobust(time_trans_loglogistic_DR,W,c=0.5,h=h_loglogistic_DR$bws[1],b=h_loglogistic_DR$bws[2],vce="nn")
fit_loglogistic_DR_hc0 <- rdrobust(time_trans_loglogistic_DR,W,c=0.5,h=h_loglogistic_DR$bws[1],b=h_loglogistic_DR$bws[2],vce="hc0")

# bootstrapping
boot_fun <- function(dat,ind){
dat=dat[ind,]
y.b<- dat$y
n <- length(y.b)
status.b <- dat$status
W.b <- dat$W

values_cox_DR.b <- external_DR(y.b,status.b,W.b,"cox")
values_lognorm_DR.b <- external_DR(y.b,status.b,W.b,"lognorm")
values_loglogistic_DR.b <- external_DR(y.b,status.b,W.b,"loglogistic")

# calculation of transformed responses
# IPCW
time_trans_IPCW.b <- values_cox_DR.b[(nu+1):(2*nu)] 
time_trans_cox_DR.b <- values_cox_DR.b[(nu+1):(2*nu)] + values_cox_DR.b[(3*nu+1):(4*nu)] - values_cox_DR.b[(5*nu+1):(6*nu)]
time_trans_lognorm_DR.b <- values_lognorm_DR.b[(nu+1):(2*nu)] + values_lognorm_DR.b[(3*nu+1):(4*nu)] - values_lognorm_DR.b[(5*nu+1):(6*nu)]
time_trans_loglogistic_DR.b <- values_loglogistic_DR.b[(nu+1):(2*nu)] + values_loglogistic_DR.b[(3*nu+1):(4*nu)] - values_loglogistic_DR.b[(5*nu+1):(6*nu)]  

# fit sharp design
# bandwidth : Ludwig and Miller
# vec = nearest neightbor
# IPCW
h_IPCW.b <- rdbwselect_2014(time_trans_IPCW.b,W.b,c=0.5,bwselect="CV")
fit_IPCW_nn.b <- rdrobust(time_trans_IPCW.b,W.b,c=0.5,h=h_IPCW.b$bws[1],b=h_IPCW.b$bws[2],vce="nn")

# DR
h_cox_DR.b <- rdbwselect_2014(time_trans_cox_DR.b,W.b,c=0.5,bwselect = "CV")
fit_cox_DR_nn.b <- rdrobust(time_trans_cox_DR.b,W.b,c=0.5,h=h_cox_DR.b$bws[1],b=h_cox_DR.b$bws[2],vce="nn")
h_lognorm_DR.b <- rdbwselect_2014(time_trans_lognorm_DR.b,W.b,c=0.5,bwselect = "CV")
fit_lognorm_DR_nn.b <- rdrobust(time_trans_lognorm_DR.b,W.b,c=0.5,h=h_lognorm_DR.b$bws[1],b=h_lognorm_DR.b$bws[2],vce="nn")
h_loglogistic_DR.b <- rdbwselect_2014(time_trans_loglogistic_DR.b,W.b,c=0.5,bwselect = "CV")
fit_loglogistic_DR_nn.b <- rdrobust(time_trans_loglogistic_DR.b,W.b,c=0.5,h=h_loglogistic_DR.b$bws[1],b=h_loglogistic_DR.b$bws[2],vce="nn")
return(c(fit_IPCW_nn.b$coef[1],fit_cox_DR_nn.b$coef[1],fit_lognorm_DR_nn.b$coef[1],fit_loglogistic_DR_nn.b$coef[1]))
}
dat <- data.frame(y=y,status=status,W=W)
ind = 1:nu
boot_fit <- boot(dat, boot_fun, R = 200)
betase_con_nn_boot <- apply(boot_fit[[2]],2,sd)
# estimates
betaest_con_nn <- c(fit_IPCW_nn$coef[1],fit_cox_DR_nn$coef[1],fit_lognorm_DR_nn$coef[1],fit_loglogistic_DR_nn$coef[1])
betaest_con_hc0 <- c(fit_IPCW_hc0$coef[1],fit_cox_DR_hc0$coef[1],fit_lognorm_DR_hc0$coef[1],fit_loglogistic_DR_hc0$coef[1])

# Standard error
# nn : nearest neighborhood
# hc0 : plug - in approach
betase_con_nn <- c(fit_IPCW_nn$se[1],fit_cox_DR_nn$se[1],fit_lognorm_DR_nn$se[1],fit_loglogistic_DR_nn$se[1])
betase_con_hc0 <- c(fit_IPCW_hc0$se[1],fit_cox_DR_hc0$se[1],fit_lognorm_DR_hc0$se[1],fit_loglogistic_DR_hc0$se[1])

# coverage
# Without bootstrap
# Convential
# nn
# IPCW
cover_con_IPCW_nn <- as.numeric(fit_IPCW_nn$coef[1] - qnorm(0.975) *  fit_IPCW_nn$se[1] <= beta30 & beta30 <= fit_IPCW_nn$coef[1] + qnorm(0.975) *  fit_IPCW_nn$se[1])
# DR
cover_con_cox_DR_nn <- as.numeric(fit_cox_DR_nn$coef[1] - qnorm(0.975) *  fit_cox_DR_nn$se[1] <= beta30 & beta30 <= fit_cox_DR_nn$coef[1] + qnorm(0.975) *  fit_cox_DR_nn$se[1])
cover_con_lognorm_DR_nn <- as.numeric(fit_lognorm_DR_nn$coef[1] - qnorm(0.975) *  fit_lognorm_DR_nn$se[1] <= beta30 & beta30 <= fit_lognorm_DR_nn$coef[1] + qnorm(0.975) *  fit_lognorm_DR_nn$se[1])
cover_con_loglogistic_DR_nn <- as.numeric(fit_loglogistic_DR_nn$coef[1] - qnorm(0.975) *  fit_loglogistic_DR_nn$se[1] <= beta30 & beta30 <= fit_loglogistic_DR_nn$coef[1] + qnorm(0.975) *  fit_loglogistic_DR_nn$se[1])
# hc0
# IPCW
cover_con_IPCW_hc0 <- as.numeric(fit_IPCW_hc0$coef[1] - qnorm(0.975) *  fit_IPCW_hc0$se[1] <= beta30 & beta30 <= fit_IPCW_hc0$coef[1] + qnorm(0.975) *  fit_IPCW_hc0$se[1])
# DR
cover_con_cox_DR_hc0 <- as.numeric(fit_cox_DR_hc0$coef[1] - qnorm(0.975) *  fit_cox_DR_hc0$se[1] <= beta30 & beta30 <= fit_cox_DR_hc0$coef[1] + qnorm(0.975) *  fit_cox_DR_hc0$se[1])
cover_con_lognorm_DR_hc0 <- as.numeric(fit_lognorm_DR_hc0$coef[1] - qnorm(0.975) *  fit_lognorm_DR_hc0$se[1] <= beta30 & beta30 <= fit_lognorm_DR_hc0$coef[1] + qnorm(0.975) *  fit_lognorm_DR_hc0$se[1])
cover_con_loglogistic_DR_hc0 <- as.numeric(fit_loglogistic_DR_hc0$coef[1] - qnorm(0.975) *  fit_loglogistic_DR_hc0$se[1] <= beta30 & beta30 <= fit_loglogistic_DR_hc0$coef[1] + qnorm(0.975) *  fit_loglogistic_DR_hc0$se[1])


# With bootstrap
# Conventional
# IPCW
cover_con_IPCW_nn_boot <- as.numeric(fit_IPCW_nn$coef[1] - qnorm(0.975) *  betase_con_nn_boot[1] <= beta30 & beta30 <= fit_IPCW_nn$coef[1] + qnorm(0.975) * betase_con_nn_boot[1])
# DR
cover_con_cox_DR_nn_boot <- as.numeric(fit_cox_DR_nn$coef[1] - qnorm(0.975) *  betase_con_nn_boot[2] <= beta30 & beta30 <= fit_cox_DR_nn$coef[1] + qnorm(0.975) * betase_con_nn_boot[2])
cover_con_lognorm_DR_nn_boot <- as.numeric(fit_lognorm_DR_nn$coef[1] - qnorm(0.975) *  betase_con_nn_boot[3] <= beta30 & beta30 <= fit_lognorm_DR_nn$coef[1] + qnorm(0.975) * betase_con_nn_boot[3])
cover_con_loglogistic_DR_nn_boot <- as.numeric(fit_loglogistic_DR_nn$coef[1] - qnorm(0.975) *  betase_con_nn_boot[4] <= beta30 & beta30 <= fit_loglogistic_DR_nn$coef[1] + qnorm(0.975) * betase_con_nn_boot[4])


# Collect all results
beta_est_all <- rbind(betaest_con_nn,betaest_con_hc0)
beta_se_all <- rbind(betase_con_nn,betase_con_hc0,betase_con_nn_boot)
cover_con_nn_o <- c(cover_con_IPCW_nn,cover_con_cox_DR_nn,cover_con_lognorm_DR_nn,cover_con_loglogistic_DR_nn)
cover_con_hc0_o <- c(cover_con_IPCW_hc0,cover_con_cox_DR_hc0,cover_con_lognorm_DR_hc0,cover_con_loglogistic_DR_hc0)
cover_con_boot <- c(cover_con_IPCW_nn_boot,cover_con_cox_DR_nn_boot,cover_con_lognorm_DR_nn_boot,cover_con_loglogistic_DR_nn_boot)
cover_all <- rbind(cover_con_nn_o,cover_con_hc0_o,cover_con_boot)

colnames(beta_est_all) <- c("IPCW","Cox","lognorm","log-logistic")
rownames(beta_est_all) <- c("nn","hc0")
colnames(beta_se_all) <- c("IPCW","Cox","lognorm","log-logistic")
rownames(beta_se_all) <- c("nn","hc0","bootstrap")
colnames(cover_all) <- c("IPCW","Cox","lognorm","log-logistic")
rownames(cover_all) <- c("nn","hc0","bootstrap")

beta_est_all
beta_se_all
cover_all


#> beta_est_all
#           IPCW       Cox   lognorm log-logistic
#nn  -0.04767822 0.8066783 0.8264288    0.8259672
#hc0 -0.04767822 0.8066783 0.8264288    0.8259672
#> beta_se_all
#              IPCW        Cox    lognorm log-logistic
#nn        1.195160 0.08726412 0.09854786   0.09685139
#hc0       1.191982 0.09046522 0.09945137   0.09934589
#bootstrap 1.213474 0.09269730 0.09372343   0.09657685
#> cover_all
#          IPCW Cox lognorm log-logistic
#nn           1   0       1            1
#hc0          1   0       1            1
#bootstrap    1   0       1            1

