# rescaling (auxiliary)
scaleFun <- function(x, scaling, par) {
  mu <- par[1]
  sig <- par[2]
  if(scaling==1) {
    # centering
    x-mu
    } else if(scaling==2) {
    # standardization
    (x-mu)/sig  
    } else if(scaling==3) {
    # division by the mean
    x/mu
    } else if(scaling==4) {
    # log centering
    log(x)-log(mu)
    } else {
    x  
    }
  }

# inverse rescaling (auxiliary)
scaleFun_inv <- function(x, scaling, par) {
  if(scaling==1) {
    # centering
    x+par[1]
    } else if(scaling==2) {
    # standardization
    x*par[2]+par[1]
    } else if(scaling==3) {
    # division by the mean
    x*par[1]
    } else if(scaling==4) {
    # log division by the mean
    exp(x)*par[1]
    } else {
    x  
    }
  }

# multinormal density (auxiliary)
logdmN <- function(x,mu,S) {
  dS <- det(S)
  if(dS>0) {
    cost <- -ncol(S)/2*log(2*pi)-0.5*log(dS)
    W <- solve(S)
    ll <- c()
    for(i in 1:nrow(x)){
      idx <- as.vector(t(x[i,]-mu[i,]))
      ll[i] <- cost-0.5*t(idx)%*%W%*%(idx)
      }
    ll
    } else {
    rep(-Inf,length(x))
    }
  }

# smooth covariance matrix (auxiliary)
smoothFun <- function(S) {
  tt <- tryCatch(solve(S), error=function(e){e})
  if(is(tt,"error")) {
    #print("smoothed")  ## <-- lisciamento
    as.matrix(nearPD(S)$mat)
    } else {
    S
    }
  }

# function for imputation (auxiliary)
imputFun <- function(xdat, tval, beta, S, d) {
  newdat <- xdat
  for(i in 1:nrow(xdat)) {
    iNA <- which(is.na(xdat[i,]))
    if(length(iNA)>0) {
      ix <- xdat[i,]
      it <- c(1,tval[i]^(1:d))
      imu <- t(beta)%*%it
      iO <- which(!is.na(xdat[i,]))
      if(length(iO)>0) {
        s22 <- S[iO,iO,drop=F]
        s22_inv <- solve(s22)
        ijdiff <- as.vector(t(ix[iO]-imu[iO]))
        newdat[i,iNA] <- imu[iNA]+S[iNA,iO,drop=F]%*%s22_inv%*%ijdiff
        } else {
        newdat[i,iNA] <- imu[iNA]
        }
      }
    }
  newdat
  }

# compute appa (auxiliary)
appaCalc <- function(tab) {
  cl <- apply(tab,1,which.max)
  appa <- c()
  for(i in 1:ncol(tab)) {
    appa[i] <- mean(tab[which(cl==i),i])
    }
  names(appa) <- colnames(tab)
  appa
  }

# compute number of parameters (auxiliary)
nparCalc <- function(beta) {
  ng <- length(beta)
  np <- ncol(beta[[1]])
  sum(sapply(beta,function(z){sum(z!=0)}))+ng*(1+np*(np+1)/2)-1
  }

# compute information criteria (auxiliary)
icCalc <- function(logLik, npar, ss) {
  a <- -2*logLik
  c(aic=a+2*npar,
    bic=a+npar*log(ss),
    #aicc=a+2*npar*(1+(npar+1)/(ss-npar-1)),
    caic=a+npar*(log(ss)+1),
    ssbic=a+npar*log((ss+2)/24),
    hqic=a+npar*2*log(log(ss)))
  }

# pruning (auxiliary)
pruneFun <- function(beta, posterior, data) {
  ng <- length(beta)
  nomi <- colnames(beta[[1]])
  pnam <- rownames(beta[[1]])
  d <- nrow(beta[[1]])-1
  cou <- rownames(posterior)
  t <- as.numeric(data[,2])-min(as.numeric(data[,2]))+1
  weiMat <- matrix(nrow=nrow(data),ncol=ng)
  for(i in 1:length(cou)) {
    ind <- which(data[,1]==cou[i])
    for(j in 1:ng) {
      weiMat[ind,j] <- posterior[i,j]
      }
    }
  reg <- beta <- S <- vector("list",length=ng)
  postd <- matrix(nrow=nrow(posterior),ncol=ng)
  names(reg) <- names(beta) <- names(S) <- 1:ng
  #
  modSel <- function(xname, wei) {
    form <- formula(paste0(xname,"~",paste("I(t^",1:d,")",collapse="+")))
    mod <- lm(form, data=data, weights=wei)
    deg <- d
    fine <- 0
    while(fine==0) {
      if(deg<=0) {
        fine <- 1
        } else {
        pval <- suppressWarnings(summary(mod)$coef)[,4]
        p_last <- pval[length(pval)]
        if(is.na(p_last) | p_last>0.05) {
          deg <- deg-1
          if(deg>=1) {
            form <- formula(paste0(xname,"~",paste("I(t^",1:deg,")",collapse="+")))
            } else {
            form <- formula(paste0(xname,"~1"))
            fine <- 1
            }
          mod <- lm(form, data=data, weights=wei)
          } else {
          fine <- 1  
          }
        }
      }
    mod$call$formula <- form
    mod$call$weights <- mod$call$data <- NULL
    mod
    }
  #
  for(i in 1:ng) {
    ireg <- list()
    ibhat <- matrix(0,nrow=d+1,ncol=length(nomi))
    rownames(ibhat) <- pnam
    colnames(ibhat) <- nomi
    for(j in 1:length(nomi)) {
      ijmod <- modSel(xname=nomi[j], wei=weiMat[,i])
      ireg[[j]] <- ijmod
      ijb <- ijmod$coefficients
      ijb[which(is.na(ijb))] <- 0  ## gestione singolarita'
      ibhat[1:length(ijb),j] <- ijb
      }
    names(ireg) <- nomi
    beta[[i]] <- ibhat
    ires <- do.call(cbind,lapply(ireg,function(x){x$residuals}))
    ifit <- do.call(cbind,lapply(ireg,function(x){x$fitted.values}))
    iS <- matrix(0,nrow=length(nomi),ncol=length(nomi))
    rownames(iS) <- colnames(iS) <- nomi
    iswei <- sum(weiMat[,i])
    for(j in 1:nrow(ires)) {
      ijr <- as.vector(t(ires[j,]))
      iS <- iS+weiMat[j,i]/iswei*(ijr%*%t(ijr))
      }
    S[[i]] <- smoothFun(iS)
    reg[[i]] <- ireg
    for(w in 1:length(cou)) {
      auxw <- which(data[,1]==cou[w])
      if(length(nomi)>1) {
        wdat <- as.matrix(data[auxw,nomi,drop=F])
        wfit <- ifit[auxw,nomi,drop=F]
        ijD <- sum(logdmN(wdat, wfit, S[[i]]))
        } else {
        ijD <- sum(dnorm(data[auxw,nomi], ifit[auxw], sqrt(S[[i]]),log=T))
        }
      postd[w,i] <- pldBound(ijD+log(mean(posterior[,i])))
      }
    }
  ll <- sum(log(apply(exp(postd),1,sum)))
  list(beta=beta,S=S,reg=reg,logLik=ll)
  }

# bound posterior log density (auxiliary)
pldBound <- function(x) {
  max(min(x,709.782),-7.451e+2)
  }

# fit wls (auxiliary)
wlsFit <- function(x.names,data,t,weights=NULL,d=1) {
  modList <- list()
  beta <- matrix(nrow=d+1,ncol=length(x.names))
  res <- cbind()
  for(i in 1:length(x.names)) {
    iform <- formula(paste0(x.names[i],"~",paste("I(t^",1:d,")",collapse="+")))
    imod <- lm(iform, data=data, weights=weights)
    imod$call$formula <- iform
    imod$call$data <- NULL
    #deparse(substitute(data))
    modList[[i]] <- imod
    icoef <- imod$coefficients
    icoef[which(is.na(icoef))] <- 0  ## gestione singolarita'
    beta[,i] <- icoef
    res <- cbind(res, imod$residuals)
    }
  names(modList) <- colnames(beta) <- colnames(res) <- x.names
  rownames(beta) <- c("(Intercept)",paste0("I(t^",1:d,")"))
  if(is.null(weights)) {
    S <- cov(res)
    } else {
    S <- matrix(0,nrow=length(x.names),ncol=length(x.names))
    rownames(S) <- colnames(S) <- x.names
    swei <- sum(weights)
    for(i in 1:nrow(res)) {
      ir <- as.vector(t(res[i,]))
      S <- S+weights[i]/swei*(ir%*%t(ir))
      }
    }
  list(fit=modList,beta=beta,S=smoothFun(S))
  }

# run em algorithm (auxiliary)
gbmtFit <- function(x.names,unit,time,ng,d,data,pruning,tol,maxit,init,quiet,id_restart,nch0) {
  data[,unit] <- factor(data[,unit])
  tnam <- levels(factor(data[,time]))
  tval <- as.numeric(data[,time]-min(data[,time])+1)
  ismiss <- sum(is.na(data[,x.names]))>0
  cou <- levels(factor(data[,unit]))
  n <- length(cou)
  np <- length(x.names)
  nt <- length(tnam)
  if(!is.null(id_restart)) {
    mstr0 <- paste0("Restart ",id_restart," - ")
    } else {
    mstr0 <- ""
    }
  # create objects
  if(is.null(init)) {
    Z <- Z0 <- sample(rep(1:ng, length=n))
    } else {
    Z <- Z0 <- init
    }
  names(Z) <- names(Z0) <- cou
  Xmat <- matrix(nrow=nt,ncol=d+1)
  for(i in 0:d) Xmat[,i+1] <- sort(unique(tval))^i
  rownames(Xmat) <- tnam
  colnames(Xmat) <- paste0("I(t^",0:d,")")
  postd <- postp <- matrix(nrow=n,ncol=ng)
  rownames(postd) <- rownames(postp) <- cou
  p0 <- prop.table(table(factor(Z,levels=1:ng)))
  beta <- S <- reg <- vector("list",length=ng)
  dataI <- data
  if(ismiss) {
    for(j in 1:length(x.names)) {
      ijna <- which(is.na(data[,x.names[j]]))
      if(length(ijna)>0) dataI[ijna,x.names[j]] <- mean(data[,x.names[j]],na.rm=T)
      }
    dataI_list <- vector("list",length=ng)
    }
  form <- formula(paste("cbind(",paste(x.names,collapse=","),") ~ ",paste("I(t^",1:d,")",collapse="+"),sep=""))
  # initialization
  for(i in 1:ng) {
    iwei <- rep(0,nrow(data))
    iwei[which(data[,unit]%in%cou[which(Z==i)])] <- 1
    imod <- wlsFit(x.names=x.names, data=dataI, t=tval, weights=iwei, d=d)
    reg[[i]] <- imod$fit
    beta[[i]] <- imod$beta
    S[[i]] <- imod$S
    for(w in 1:n) {
      auxw <- which(data[,unit]==cou[w])
      wdat <- as.matrix(dataI[auxw,x.names,drop=F])
      if(np>1) {
        ijD <- sum(logdmN(wdat, Xmat%*%beta[[i]], S[[i]]))
        } else {
        ijD <- sum(dnorm(dataI[auxw,x.names], Xmat%*%beta[[i]], sqrt(S[[i]]),log=T))
        }
      postd[w,i] <- pldBound(ijD+log(p0[i]))
      }
    }
  ll_old <- sum(log(apply(exp(postd),1,sum)))
  fine <- count <- count2 <- 0
  if(quiet==F) {
    mstr <- paste0(mstr0,"EM iteration ",count,". Log likelihood: ",round(ll_old,4))
    nch <- nchar(mstr)
    if(nch<nch0) {
      estr <- rep(" ",nch0-nch)
      } else {
      estr <- ""
      }
    cat('\r',mstr,estr)
    flush.console()
    } else {
    nch <- 0  
    }
  p0_old <- p0
  beta_old <- beta
  S_old <- S
  reg_old <- reg
  # begin EM cycle
  while(fine==0) {
    count <- count+1
    # e-step: compute posterior
    for(i in 1:nrow(postd)) {
      postp[i,] <- exp(postd[i,])/sum(exp(postd[i,]))
      }
    Z_old <- Z
    Z <- apply(postp,1,which.max)
    # m-step: calcolo prior, beta, sigma
    p0 <- colMeans(postp)
    for(i in 1:ng) {
      iwei <- c()
      for(j in 1:length(cou)) {
        iwei[which(data[,unit]==cou[j])] <- postp[j,i]
        }
      if(ismiss) {
        idat <- dataI_list[[i]] <- imputFun(xdat=data[,x.names,drop=F], tval=tval, beta=beta[[i]], S=S[[i]], d=d)
        } else {
        idat <- data[,x.names,drop=F]
        }
      if(ng==1 | var(iwei)>0) {
        imod <- wlsFit(x.names=x.names, data=idat, t=tval, weights=iwei, d=d)
        reg[[i]] <- imod$fit
        beta[[i]] <- imod$beta
        S[[i]] <- imod$S
        for(w in 1:n) {
          auxw <- which(data[,unit]==cou[w])
          wdat <- as.matrix(idat[auxw,x.names,drop=F])
          if(np>1) {
            ijD <- sum(logdmN(wdat, Xmat%*%beta[[i]], S[[i]]))
            } else {
            ijD <- sum(dnorm(wdat, Xmat%*%beta[[i]], sqrt(S[[i]]),log=T))
            }
          postd[w,i] <- pldBound(ijD+log(p0[i]))
          }
        } else {
        postd[,i] <- -Inf  ## <-- gruppo vuoto
        }
      }
    # compute log likelihood
    ll_new <- sum(log(apply(exp(postd),1,sum)))
    # check convergence
    if(ll_new>=ll_old) {
      if(ll_new-ll_old<tol) fine <- 1
      } else {
      #print(paste0("Likelihood decreased: ",ll_old," -> ",ll_new))
      p0 <- p0_old
      beta <- beta_old
      S <- S_old
      reg <- reg_old
      ll_new <- ll_old
      count <- count-1
      fine <- 1
      }
    if(quiet==F) {
      mstr <- paste0(mstr0,"EM iteration ",count,". Log likelihood: ",round(ll_new,4))
      nch <- nchar(mstr)
      if(nch<nch0) {
        estr <- rep(" ",nch0-nch)
        } else {
        estr <- ""
        }
      cat('\r',mstr,estr)
      flush.console()
      nch0 <- nch
      }
    if(count>=maxit) fine <- 1
    if(sum(Z_old-Z)==0) {
      count2 <- count2+1
      if(ll_new-ll_old<tol*sqrt(count2)) fine <- 1
      } else {
      count2 <- 0
      }
    if(fine==0) {
      ll_old <- ll_new
      p0_old <- p0
      beta_old <- beta
      S_old <- S
      reg_old <- reg
      postp_old <- postp
      }
    }
  # end EM cycle
  for(i in 1:nrow(postd)) {
    postp[i,] <- exp(postd[i,])/sum(exp(postd[i,]))
    }
  Z <- apply(postp,1,which.max)
  assL <- vector("list",length=ng)
  for(i in 1:ng) {
    assL[[i]] <- sort(names(which(Z==i)))
    }
  # imputed data
  if(ismiss) {
    auxdat <- dataI_list[[1]][,x.names,drop=F]*p0[1]
    if(length(dataI_list)>1) {
      for(i in 2:length(dataI_list)) {
        auxdat <- auxdat+dataI_list[[i]][,x.names,drop=F]*p0[i]
        }
      }
    newdat <- data.frame(data[,c(unit,time)],auxdat)
    } else {
    newdat <- data[,c(unit,time,x.names)]
    }
  # eliminate empty groups
  auxchk <- which(sapply(assL,length)==0)
  if(length(auxchk)>0) {
    gOK <- setdiff(1:ng,auxchk)
    beta <- beta[gOK]
    S <- S[gOK]
    postp <- postp[,gOK,drop=F]
    reg <- reg[gOK]
    p0 <- p0[gOK]/sum(p0[gOK])
    assL <- assL[gOK]
    postd <- postd[,gOK,drop=F]
    ll_new <- sum(log(apply(exp(postd),1,sum)))
    ng <- length(gOK)
    warning("Some empty groups have been deleted")
    }
  # pruning
  if(pruning) {
    mpruned <- pruneFun(beta=beta, posterior=postp, data=newdat)
    reg <- mpruned$reg
    beta <- mpruned$beta
    S <- mpruned$S
    ll_new <- mpruned$logLik
    }
  npar <- nparCalc(beta)
  ic <- icCalc(ll_new, npar=npar, ss=nrow(newdat))
  pred <- vector("list",length=ng)
  names(pred) <- 1:ng
  for(i in 1:ng) {
    pred[[i]] <- data.frame(Xmat%*%beta[[i]])
    rownames(pred[[i]]) <- tnam
    colnames(pred[[i]]) <- x.names
    }
  names(p0) <- names(assL) <- colnames(postp) <- names(beta) <- names(S) <- names(reg) <- 1:ng
  datOK <- data[,c(unit,time,x.names)]
  rownames(datOK) <- NULL
  res <- list(call=list(x.names=x.names,unit=unit,time=time,ng=ng,d=d),
              prior=p0, beta=beta, Sigma=S,
              posterior=round(postp,4), Xmat=Xmat, fitted=pred, reg=reg,
              assign=Z, assign.list=assL,
              logLik=ll_new, npar=npar, ic=ic, appa=appaCalc(postp),
              data.orig=NULL, data.norm=newdat, data.imputed=NULL,
              em=c(n.iter=count,converged=ifelse(count>=maxit,0,1)),
              #initial=Z0,
              nch=nch)
  class(res) <- "gbmt"
  res
  }

# spline imputation
splineImp <- function(x) {
  if(sum(!is.na(x))>1) {
    xt <- length(x)
    spline(x,xout=1:xt)$y
    } else {
    xnew <- x
    xnew[which(is.na(x))] <- mean(x,na.rm=T)
    xnew
    }
  }

# initial clustering (auxiliary)
iniClust <- function(x.names,unit,time,data) {
  xunit <- factor(data[,unit])
  xtime <- as.numeric(data[,time]-min(data[,time])+1)
  cou <- levels(xunit)
  poi <- sort(unique(xtime))
  n <- length(cou)
  np <- length(x.names)
  nt <- length(poi)
  dataArr <- array(dim=c(n,nt,np))
  for(i in 1:n) {
    for(j in 1:nt) {
      ind <- which(xunit==cou[i]&xtime==poi[j])
      if(length(ind)>0) dataArr[i,j,] <- unlist(data[ind,x.names])
      }
    }
  dat <- dataArr[,1,]
  for(j in 2:nt) dat <- cbind(dat, dataArr[,j,])
  datI <- apply(dat,2,splineImp)
  datOK <- t(na.omit(t(datI)))
  rownames(datOK) <- cou
  hclust(dist(datOK), method="ward.D2")
  }

# fit gbmt
gbmt <- function(x.names,unit,time,ng=1,d=2,data,scaling=2,pruning=TRUE,nstart=NULL,tol=1e-4,maxit=1000,quiet=FALSE) {
  #
  if(missing(data)) stop("Missing argument 'data'")
  if(!identical(class(data), "data.frame")) stop("Argument 'data' must be a data.frame")
  #
  if(missing(unit)) stop("Missing argument 'unit'")
  if(!is.character(unit) || length(unit)!=1) stop("Argument 'unit' must be a character vector of length 1")
  if((unit%in%colnames(data))==F) stop("Variable '",unit,"' not found",sep="")
  if(sum(is.na(data[,unit]))>0) stop("Variable '",unit,"' cannot contain missing values")
  #
  if(missing(time)) stop("Missing argument 'time'")
  if(!is.character(time) || length(time)!=1) stop("Argument 'time' must be a character vector of length 1")
  if((time%in%colnames(data))==F) stop("Variable '",time,"' not found",sep="")
  if(!is.numeric(data[,time]) & inherits(data[,time],'Date')==F) stop("Variable '",time,"' must be either numeric or date")
  if(sum(is.na(data[,time]))>0) stop("Variable '",time,"' contains missing values")
  #
  if(!is.numeric(ng) || length(ng)!=1 || ng<=0 || ng!=round(ng)) stop("Argument 'ng' must be a positive integer number")
  if(!is.numeric(d) || length(d)!=1 || d<=0 || d!=round(d)) stop("Argument 'd' must be a positive integer number")
  data[,unit] <- factor(data[,unit])
  cou <- levels(data[,unit])
  if(ng>length(cou)) stop("The number of groups cannot be greater than the number of units")
  #
  if(missing(x.names)) stop("Missing argument 'x.names'")
  if(!is.character(x.names) || length(x.names)<1) stop("Argument 'x.names' must be a character vector of length 1 or greater")
  auxchk <- setdiff(x.names, colnames(data))
  if(length(auxchk)>0) stop("Variable '",auxchk[1],"' not found",sep="")
  for(i in 1:length(x.names)) {
    if(!is.numeric(data[,x.names[i]])) {
      stop("Variable '",x.names[i],"' is not numeric",sep="")      
      }
    if(sum(!is.na(data[,x.names[i]]))==0) {
      stop("Variable '",x.names[i],"' is completely missing",sep="")      
      }
    }
  if(!is.numeric(scaling)) {
    scaling <- 0
    } else {
    auxscal <- intersect(scaling,0:4)
    if(length(auxscal)==0) auxscal <- 0 else auxscal <- auxscal[1]
    scaling <- auxscal
    }
  if(scaling %in% 3:4) {
    for(i in 1:length(x.names)) {
      if(sum(data[,x.names[i]]<=0,na.rm=T)>0) stop("Variable '",x.names[i],"' contains zero or negative values: scaling=",scaling," cannot be applied",sep="")
      }
    }
  if(!is.null(nstart) && (length(nstart)!=1 || nstart<=0 || nstart!=round(nstart))) stop("Argument 'nstart' must be either NULL or a positive integer number")
  if(!is.numeric(tol) || length(tol)!=1 || tol<=0) stop("Argument 'tol' must be a positive real number")
  if(!is.numeric(maxit) || length(maxit)!=1 || maxit<=0 || maxit!=round(maxit)) stop("Argument 'maxit' must be a positive integer number")
  #
  pruning <- pruning[1]
  if(is.na(pruning)||(!is.logical(pruning)|is.null(pruning))) pruning <- TRUE
  quiet <- quiet[1]
  if(is.na(quiet)||(!is.logical(quiet)|is.null(quiet))) quiet <- FALSE
  #
  # sort data by time
  for(i in 1:length(cou)) {
    ind <- which(data[,unit]==cou[i])
    idat <- data[ind,]
    if(sum(duplicated(idat[,time]))>0) stop("Unit '",cou[i],"' has duplicated time points")
    data[ind,] <- idat[order(idat[,time]),]
    }
  # rescaling
  dataOK <- data
  for(i in 1:length(cou)) {
    ind <- which(data[,unit]==cou[i])
    for(j in 1:length(x.names)) {
      ijdat <- data[ind,x.names[j]]
      ijpar <- c(mean(ijdat,na.rm=T),sd(ijdat,na.rm=T))
      if(is.na(ijpar[1])) ijpar[1] <- mean(data[,x.names[j]],na.rm=T)
      if(is.na(ijpar[2])|ijpar[2]==0) ijpar[2] <- sd(data[,x.names[j]],na.rm=T)
      dataOK[ind,x.names[j]] <- scaleFun(ijdat, scaling=scaling, par=ijpar)
      }
    }
  if(!is.null(nstart)) {
    mOK <- gbmtFit(x.names=x.names,unit=unit,time=time,ng=ng,d=d,data=dataOK,pruning=pruning,tol=tol,maxit=maxit,init=NULL,quiet=quiet,id_restart=1,nch0=0)
    res <- c(logLik=mOK$logLik,mOK$em)
    #iniMat <- rbind(mOK$initial)
    #finMat <- rbind(mOK$assign)
    nch0 <- mOK$nch
    if(nstart>1) {
      for(i in 2:nstart) {
        m0 <- gbmtFit(x.names=x.names,unit=unit,time=time,ng=ng,d=d,data=dataOK,pruning=pruning,tol=tol,maxit=maxit,init=NULL,quiet=quiet,id_restart=i,nch0=nch0)
        res <- rbind(res,(c(logLik=m0$logLik,m0$em)))
        #iniMat <- rbind(iniMat,m0$initial)
        #finMat <- rbind(finMat,m0$assign)
        if(m0$logLik>mOK$logLik) mOK <- m0
        nch0 <- m0$nch
        }
      }
    } else {
    #ini0 <- rep(1:ng,length=length(cou))
    #names(ini0) <- sort(cou)
    cl0 <- iniClust(x.names=x.names,unit=unit,time=time,data=dataOK)
    ini0 <- cutree(cl0, k=ng)
    mOK <- gbmtFit(x.names=x.names,unit=unit,time=time,ng=ng,d=d,data=dataOK,pruning=pruning,tol=tol,maxit=maxit,init=ini0,quiet=quiet,id_restart=NULL,nch0=0)
    res <- rbind(c(logLik=mOK$logLik,mOK$em))
    #iniMat <- rbind(mOK$initial)
    #finMat <- rbind(mOK$assign)
    }
  if(quiet==F) cat("\n")
  rownames(res) <- NULL
  mOK$data.orig <- data[,c(unit,time,x.names)]
  if(sum(is.na(data[,x.names]))>0) { 
    mu <- do.call(rbind,lapply(split(data,data[,unit]),function(x){
      apply(x[,x.names,drop=F],2,mean,na.rm=T)
      }))
    dataI <- mOK$data.norm
    for(i in 1:length(cou)) {
      ind <- which(data[,unit]==cou[i])
      for(j in 1:length(x.names)) {
        ijdat <- data[ind,x.names[j]]
        ijpar <- c(mean(ijdat,na.rm=T),sd(ijdat,na.rm=T))
        if(is.na(ijpar[1])) ijpar[1] <- mean(data[,x.names[j]],na.rm=T)
        if(is.na(ijpar[2])|ijpar[2]==0) ijpar[2] <- sd(data[,x.names[j]],na.rm=T)
        dataI[ind,x.names[j]] <- scaleFun_inv(mOK$data.norm[ind,x.names[j]], scaling=scaling, par=ijpar)
        }
      }
    #
    mOK$data.imputed <- dataI
    } else {
    mOK$data.imputed <- data[,c(unit,time,x.names)]
    }
  mOK$em <- res
  mOK$call$scaling <- scaling
  mOK$call$pruning <- pruning
  mOK$call$nstart <- nstart
  mOK$call$tol <- tol
  mOK$call$maxit <- maxit
  #rownames(iniMat) <- rownames(finMat) <- NULL
  #mOK$initial <- iniMat
  #mOK$final <- finMat
  mOK$nch <- NULL
  mOK
  }

# print method
print.gbmt <- function(x, ...) {
  gdis <- table(factor(x$assign,levels=1:x$call$ng))
  for(i in 1:x$call$ng) {
    cat("Group ",i,": ",gdis[i]," units (APPA: ",round(x$appa[i],4),")",sep="","\n")
    print(t(x$beta[[i]]))
    if(i<length(gdis)) cat("\n")
    }
  }

# summary method
summary.gbmt <- function(object, ...) {
  suppressWarnings(lapply(object$reg, function(x){
    lapply(x, summary, ...)
    }))
  }

# coef method
coef.gbmt <- function(object, ...) {
  object$beta
  }

# residuals method
residuals.gbmt <- function(object, ...) {
  lapply(object$reg, function(x) {
    data.frame(
      object$data.orig[,c(object$call$unit,object$call$time)],
      do.call(cbind,lapply(x,residuals))
      )
    })
  }

# fitted method
fitted.gbmt <- function(object, ...) {
  lapply(object$reg, function(x) {
    data.frame(
      object$data.orig[,c(object$call$unit,object$call$time)],
      do.call(cbind,lapply(x,fitted))
      )
    })
  }

# logLik method
logLik.gbmt <- function(object, ...) {
  ll <- object$logLik
  attr(ll,"df") <- nparCalc(object$beta)
  class(ll) <- "logLik"
  ll
  }

# extractAIC method
extractAIC.gbmt <- function(fit, scale, k=2, ...) {
  npar <- nparCalc(fit$beta)
  c(npar, -2*fit$logLik+k*npar)
  }

# AIC method
AIC.gbmt <- function(object, k=2, ...) {
  -2*object$logLik+k*nparCalc(object$beta)
  }

# BIC method
BIC.gbmt <- function(object, ...) {
  -2*object$logLik+nparCalc(object$beta)*log(nrow(object$data.imputed))
  }

# predict method
predict.gbmt <- function(object, unit=NULL, n.ahead=0, bands=TRUE, conf=0.95, in.sample=FALSE, ...) {
  if(!is.null(unit)) {
    if(length(unit)>1) stop("Argument 'unit' must be of length 1")
    unitOK <- levels(factor(object$data.orig[,object$call$unit]))
    if((unit%in%unitOK)==F) stop("Unknown unit '",unit,"'")
    }
  #
  bands <- bands[1]
  if(is.na(bands)||(!is.logical(bands)|is.null(bands))) bands <- TRUE
  in.sample <- in.sample[1]
  if(is.na(in.sample)||(!is.logical(in.sample)|is.null(in.sample))) in.sample <- FALSE
  #
  if(!is.numeric(n.ahead)) stop("Argument 'n.ahead' must be a non-negative integer number")
  n.ahead <- max(n.ahead,na.rm=T)
  if(n.ahead<0 || n.ahead!=round(n.ahead)) stop("Argument 'n.ahead' must be a non-negative integer number")
  #
  ## <-- gestire n.ahead vettore
  #
  if(identical(n.ahead,0) && in.sample==F) in.sample <- T
  if(bands) {
    if(length(conf)>1) conf <- conf[1]
    if(!is.numeric(conf) || conf<0 || conf>=1) stop("Argument 'conf' must be a non-negative value less than 1")
    plab <- signif((1-conf)/2*100,2)
    }
  reg <- object$reg
  Xmat <- object$Xmat
  t0 <- min(object$data.orig[,object$call$time])-1
  nt <- max(Xmat[,2])
  tdat <- c()
  if(in.sample || identical(n.ahead,0)) tdat <- data.frame(t=Xmat[,2])
  if(n.ahead>0) tdat <- data.frame(t=c(tdat$t,(nt+1):(nt+n.ahead)))
  if(is.numeric(object$data.orig[,object$call$time])) {
    tnam <- t0+tdat$t
    } else {
    tnam <- as.Date(tdat$t,t0)
    }
  rownames(tdat) <- tnam
  pr <- list()
  for(i in 1:length(reg)) {
    suppressWarnings(
      if(bands) {
        ipr <- lapply(reg[[i]], function(z) {
          m <- predict.lm(z, newdata=tdat, interval="prediction", level=conf)
          colnames(m) <- c("mean",paste0(c(plab,100-plab),"%"))
          m
          })
        } else {
        ipr <- lapply(reg[[i]], function(z) {
          m <- as.matrix(predict.lm(z, newdata=tdat))
          colnames(m) <- "mean"
          m
          })
        }
      )
    pr[[i]] <- ipr
    }
  names(pr) <- names(reg)
  if(!is.null(unit)) {
    ind <- which(object$data.orig[,object$call$unit]==unit)
    wei <- object$posterior[unit,]
    dat <- object$data.imputed
    pr_new <- pr[[1]]
    for(i in 1:length(pr_new)) pr_new[[i]][] <- 0
    for(i in 1:length(pr_new)) {
      ipar <- c(mean(dat[ind,names(pr_new)[i]],na.rm=T),
                sd(dat[ind,names(pr_new)[i]],na.rm=T))
      if(is.na(ipar[1])) ipar[1] <- mean(dat[,names(pr_new)[i]],na.rm=T)
      if(is.na(ipar[2])|ipar[2]==0) ipar[2] <- sd(dat[,names(pr_new)[i]],na.rm=T)
      for(j in 1:length(pr)) {
        pr_new[[i]] <- pr_new[[i]]+wei[j]*scaleFun_inv(pr[[j]][[i]], scaling=object$call$scaling, par=ipar)
        }
      }
    pr_new
    } else {
    pr  
    }
  }

# check color (auxiliary)
areColors <- function(x) {
  sapply(x, function(y) {
    tryCatch(is.matrix(col2rgb(y)), error=function(e) FALSE)
    })
  }

# create transparent color (auxiliary)
t_col <- function(color, percent=50, name=NULL) {
  rgb.val <- col2rgb(color)
  percent <- max(0,min(100,percent[1]))
  tcol <- rgb(rgb.val[1], rgb.val[2], rgb.val[3], maxColorValue=255,
                alpha=(100-percent)*255/100, names=name)
  invisible(tcol)
  }

# plot method
plot.gbmt <- function(x, group=NULL, unit=NULL, x.names=NULL, n.ahead=0, bands=TRUE, conf=0.95, observed=TRUE, equal.scale=FALSE, trim=0, ylim=NULL, xlab="", ylab="",
                      titles=NULL, add.grid=TRUE, col=NULL, transparency=-1, add.legend=TRUE, pos.legend=c(0,0), cex.legend=0.6, mar=c(5.1,4.1,4.1,2.1), ...) {
  if(is.null(unit) && !is.null(group)) {
    if((group %in% names(x$reg))==F & (group %in% 1:length(x$reg))==F) {
      stop("Invalid argument 'group'. Valid values are: ",paste0(1:length(x$beta),collapse=", "))
      }
    }
  if(!is.null(unit)) {
    if(length(unit)>1) stop("Argument 'unit' must be of length 1")
    unitOK <- levels(factor(x$data.orig[,x$call$unit]))
    if((unit%in%unitOK)==F) stop("Unknown unit '",unit,"'")
    }
  if(is.numeric(n.ahead)) n.ahead <- max(n.ahead,na.rm=T)
  if(!is.numeric(n.ahead) || n.ahead<0 || n.ahead!=round(n.ahead)) stop("Argument 'n.ahead' must be a non-negative integer number")
  bands <- bands[1]
  if(is.na(bands)||(!is.logical(bands)|is.null(bands))) bands <- TRUE
  add.grid <- add.grid[1]
  if(is.na(add.grid)||(!is.logical(add.grid)|is.null(add.grid))) add.grid <- TRUE
  if(bands) {
    if(length(conf)>1) conf <- conf[1]
    if(!is.numeric(conf) || conf<0 || conf>=1) stop("Argument 'conf' must be a non-negative value less than 1")
    if(!is.numeric(transparency)) transparency <- -1
    transparency <- transparency[1]
    }
  pr <- predict.gbmt(x, group=NULL, unit=unit, n.ahead=n.ahead, bands=bands, conf=conf, in.sample=T)
  xnam <- xall <- x$call$x.names
  if(!is.null(x.names)) {
    auxchk <- setdiff(x.names,xall)
    if(length(auxchk)>0) stop("Unknown variable '",auxchk[1],"' in argument 'x.names'")
    xnam <- x.names
    }
  if(length(xnam)>1) {
    oldpar <- par(no.readonly=T)
    on.exit(par(oldpar)) 
    }
  observed <- observed[1]
  if(is.na(observed)||(!is.logical(observed)|is.null(observed))) observed <- TRUE
  equal.scale <- equal.scale[1]
  if(is.na(equal.scale)||(!is.logical(equal.scale)|is.null(equal.scale))) equal.scale <- FALSE
  if(equal.scale) {
    if(!is.numeric(trim)) trim <- 0
    trim <- trim[1]
    if(trim<0) trim <- 0
    if(trim>1) trim <- 1
    }
  auxcol <- 1:length(x$reg)
  if(!is.null(col)) {
    auxcol <- areColors(col)
    col <- col[which(auxcol)]
    if(length(col)==0) col <- NULL
    }
  if(is.null(col)) {
    if(is.null(group)&is.null(unit)) {
      col <- auxcol+1
      } else {
      col <- 1
      }
    }
  if(!is.numeric(ylim)||length(ylim)<2) ylim <- NULL else ylim <- ylim[1:2]
  if(!is.null(ylim)&&sum(abs(ylim)==Inf,na.rm=T)>0) ylim <- NULL
  Xmat <- x$Xmat
  nt <- max(Xmat[,2])
  t0 <- min(x$data.orig[,x$call$time])-1
  auxseq <- seq(1,nt+n.ahead,length=100)
  tseq <- t0+auxseq
  if(is.numeric(t0)) {
    tlim <- t0+c(1,nt+n.ahead)
    } else {
    tlim <- as.Date(c(1,nt+n.ahead),t0)
    }
  if(is.null(unit) & !is.null(group)) {
    dat <- x$data.norm
    cou <- x$assign.list[[group]]
    ind <- which(dat[,x$call$unit]%in%cou)
    ly <- list()
    for(i in 1:length(xnam)) {
      if(is.null(ylim)) {
        if(observed) {
          if(equal.scale) {
            ily1 <- range(pr)
            ily2 <- quantile(as.matrix(dat[,xall],prob=c(trim/2,1-trim/2)))
            } else {
            ily1 <- range(pr[[group]][[xnam[i]]])
            ily2 <- quantile(dat[ind,xnam[i]],prob=c(trim/2,1-trim/2))
            }
          ly[[i]] <- c(min(ily1[1],ily2[1]),max(ily1[2],ily2[2]))
          } else {
          if(equal.scale) {
            ly[[i]] <- range(pr)
            } else {
            ly[[i]] <- range(pr[[group]][[xnam[i]]])
            }
          }
        } else {
        ly[[i]] <- ylim
        }
      }
    if(length(xnam)>1) par(mar=mar,mfrow=n2mfrow(length(xnam)))
    for(i in 1:length(xnam)) {
      itit <- ifelse(is.null(titles),xnam[i],titles[i])
      plot(t0,0,type="n",ylim=ly[[i]],xlim=tlim,xlab=xlab,ylab=ylab,main=itit,...)
      if(add.grid) grid()
      if(observed) {
        for(j in 1:length(cou)) {
          ijind <- which(dat[,x$call$unit]==cou[j])
          ijt <- Xmat[as.character(dat[ijind,x$call$time]),2]
          lines(t0+ijt,dat[ijind,xnam[i]],col="grey70")
          }
        }
      if(bands) {
        suppressWarnings(
          ibands <- predict.lm(x$reg[[group]][[xnam[i]]], newdata=data.frame(t=auxseq), interval="prediction", level=conf)
          )
        if(transparency>=0) {
          polygon(c(tseq,rev(tseq)), c(ibands[,2],rev(ibands[,3])),
            border=NA, col=t_col(col[1],percent=transparency))
          } else {
          lines(tseq, ibands[,2], lty=2, col=col[1])
          lines(tseq, ibands[,3], lty=2, col=col[1])
          }  
        lines(tseq, ibands[,1], lwd=2, col=col[1])
        } else {
        suppressWarnings(
          ipr <- predict.lm(x$reg[[group]][[xnam[i]]],newdata=data.frame(t=auxseq))
          )
        lines(tseq, ipr, lwd=2, col=col[1])
        }
      if(n.ahead>0) abline(v=t0+nt, lty=2)
      box()
      }
    } else if(!is.null(unit)) {
    dat <- x$data.imputed
    cou <- unit
    wei <- x$posterior[unit,]
    ly <- list()
    ind <- which(dat[,x$call$unit]%in%unit)
    for(i in 1:length(xnam)) {
      if(is.null(ylim)) {
        if(observed) {
          ily1 <- range(pr[[xnam[i]]])
          ily2 <- quantile(dat[ind,xnam[i]],prob=c(trim/2,1-trim/2))
          ly[[i]] <- c(min(ily1[1],ily2[1]),max(ily1[2],ily2[2]))
          } else {
          ly[[i]] <- range(pr[[xnam[i]]])
          }
        } else {
        ly[[i]] <- ylim
        }
      }
    if(length(xnam)>1) par(mar=mar,mfrow=n2mfrow(length(xnam)))
    for(i in 1:length(xnam)) {
      itit <- ifelse(is.null(titles),xnam[i],titles[i])
      plot(t0,0,type="n",ylim=ly[[i]],xlim=tlim,xlab=xlab,ylab=ylab,main=itit,...)
      if(add.grid) grid()
      if(observed) {
        for(j in 1:length(cou)) {
          ijind <- which(dat[,x$call$unit]==cou[j])
          ijt <- Xmat[as.character(dat[ijind,x$call$time]),2]
          lines(t0+ijt,dat[ijind,xnam[i]],col="grey70")
          }
        }
      ipar <- c(
        mean(dat[which(dat[,x$call$unit]==unit),xnam[i]],na.rm=T),
        sd(dat[which(dat[,x$call$unit]==unit),xnam[i]],na.rm=T)
        )
      if(is.na(ipar[1])) ipar[1] <- mean(dat[,xnam[i]],na.rm=T)
      if(is.na(ipar[2])|ipar[2]==0) ipar[2] <- sd(dat[,xnam[i]],na.rm=T)
      if(bands) {
        ibandsL <- list()
        for(j in 1:length(x$reg)) {
          suppressWarnings(
            ibandsL[[j]] <- wei[j]*predict.lm(x$reg[[j]][[xnam[i]]], newdata=data.frame(t=auxseq), interval="prediction", level=conf)
            )
          }
        ibands_mix <- ibandsL[[1]]
        ibands_mix[] <- 0
        for(j in 1:length(ibandsL)) {
          ibands_mix <- ibands_mix+ibandsL[[j]]
          }
        ibands <- apply(ibands_mix, 2, scaleFun_inv, scaling=x$call$scaling, par=ipar)
        if(transparency>=0) {
          polygon(c(tseq,rev(tseq)), c(ibands[,2],rev(ibands[,3])),
            border=NA, col=t_col(col[1],percent=transparency))
          } else {
          lines(tseq, ibands[,2], lty=2, col=col[1])
          lines(tseq, ibands[,3], lty=2, col=col[1])
          }  
        lines(tseq, ibands[,1], lwd=2, col=col[1])
        } else {
        iprL <- list()
        for(j in 1:length(x$reg)) {
          suppressWarnings(
            iprL[[j]] <- wei[j]*predict.lm(x$reg[[j]][[xnam[i]]], newdata=data.frame(t=auxseq))
            )
          }
        ipr_mix <- iprL[[1]]
        ipr_mix[] <- 0
        for(j in 1:length(iprL)) {
          ipr_mix <- ipr_mix+iprL[[j]]
          }
        ipr <- scaleFun_inv(ipr_mix, scaling=x$call$scaling, par=ipar)
        lines(tseq, ipr, lwd=2, col=col[1])
        }
      if(n.ahead>0) abline(v=t0+nt, lty=2)
      box()
      }
    } else {
    add.legend <- add.legend[1]
    if(is.na(add.legend)||(!is.logical(add.legend)|is.null(add.legend))) add.legend <- TRUE
    if(add.legend) {
      if(!is.numeric(pos.legend)) cex.legend <- c(0,0)
      pos.legend <- unname(c(pos.legend,0)[1:2])
      if(!is.numeric(cex.legend)) cex.legend <- 0.6
      cex.legend <- cex.legend[1]
      }
    dat <- x$data.norm
    cou <- unlist(x$assign.list)
    ind <- 1:nrow(dat)
    ly <- list()
    for(i in 1:length(xnam)) {
      if(is.null(ylim)) {
        if(equal.scale) {
          ly[[i]] <- range(pr)
          } else {
          ly[[i]] <- range(lapply(pr,function(z){z[[xnam[i]]]}))
          }
        } else {
        ly[[i]] <- ylim
        }
      }
    if(length(xnam)>1) par(mar=mar,mfrow=n2mfrow(length(xnam)))
    for(i in 1:length(xnam)) {
      itit <- ifelse(is.null(titles),xnam[i],titles[i])
      plot(t0,0,type="n",ylim=ly[[i]],xlim=tlim,xlab=xlab,ylab=ylab,main=itit,...)
      if(add.grid) grid()
      for(j in 1:length(x$reg)) {
        #if(observed) {
        #  for(k in 1:length(cou[[j]])) {
        #    ind <- which(dat[,x$call$unit]==cou[[j]][k])
        #    ijkt <- Xmat[as.character(dat[ind,x$call$time]),2]
        #    lines(t0+ijkt,dat[ind,xnam[i]],col=t_col(col[j],percent=0.5))
        #    }
        #  }
        if(bands) {
          suppressWarnings(
            ijbands <- predict.lm(x$reg[[j]][[xnam[i]]], newdata=data.frame(t=auxseq), interval="prediction", level=conf)
            )
          if(transparency>=0) {
            polygon(c(tseq,rev(tseq)), c(ijbands[,2],rev(ijbands[,3])),
              border=NA, col=sapply(col[j],t_col,percent=transparency))
            } else {
            lines(tseq, ijbands[,2], lty=2, col=col[j])
            lines(tseq, ijbands[,3], lty=2, col=col[j])
            }
          lines(tseq, ijbands[,1], lwd=2, col=col[j])
          } else {
          suppressWarnings(
            ijpr <- predict.lm(x$reg[[j]][[xnam[i]]],newdata=data.frame(t=auxseq))
            )
          lines(tseq, ijpr, lwd=2, col=col[j])
          }
        }
      if(add.legend) legend("topleft", legend=1:length(x$reg), col=col, lty=1, bty="n", horiz=T, cex=cex.legend, xpd=!identical(pos.legend,0), inset=pos.legend)
      if(n.ahead>0) abline(v=t0+nt, lty=2)
      box()
      }
    }
  #if(!is.null(main)) mtext(main,side=3,outer=T)
  }

# compute posterior probabilities for a new unit
posterior <- function(x, newdata=NULL) {
  if(!identical(class(x),"gbmt")) stop("Argument 'x' must be an object of class 'gbmt'")
  if(is.null(newdata)) {
    x$posterior
    } else {
    if(!identical(class(newdata),"data.frame")) stop("Argument 'newdata' must be NULL or an object of class 'data.frame'")
    xtime <- x$call$time
    if((xtime%in%colnames(newdata))==F) stop("Variable '",xtime,"' not found in 'newdata'")
    xnam <- x$call$x.names
    newdataS <- newdata
    for(i in 1:length(xnam)) {
      if((xnam[i]%in%colnames(newdata))==F) stop("Variable '",xnam[i],"' not found in 'newdata'")
      if(sum(is.na(newdata[,xnam[i]]))>0) stop("Variable '",xnam[i],"' contains missing values")
      }
    reg <- x$reg
    beta <- x$beta
    S <- x$Sigma
    prior <- x$prior
    xuni <- x$call$unit
    if(xuni%in%colnames(newdata)) {
      datList <- split(newdata, as.character(newdata[,xuni]))
      } else {
      datList <- list(newdata)
      }
    res <- list()
    for(w in 1:length(datList)) {
      tval <- as.numeric(datList[[w]][,xtime]-min(x$data.orig[,xtime])+1)
      auxdat <- datList[[w]][,xnam,drop=F]
      for(j in 1:length(xnam)) {
        ijpar <- c(mean(auxdat[,xnam[j]],na.rm=T), sd(auxdat[,xnam[j]],na.rm=T))
        if(is.na(ijpar[1])) ijpar[1] <- mean(x$data.imputed[,xnam[j]],na.rm=T)
        if(is.na(ijpar[2])|ijpar[2]==0) ijpar[2] <- sd(x$data.imputed[,xnam[j]],na.rm=T)
        auxdat[,xnam[j]] <- scaleFun(auxdat[,xnam[j]], scaling=x$call$scaling, par=ijpar)
        }
      pld <- matrix(nrow=nrow(auxdat),ncol=length(beta))
      for(i in 1:length(beta)) {
        imu <- matrix(nrow=nrow(auxdat),ncol=length(xnam))
        for(j in 1:length(xnam)) {
          imu[,j] <- predict.lm(reg[[i]][[xnam[j]]], data.frame(t=tval))
          }
        pld[,i] <- logdmN(auxdat,imu,S[[i]])
        }
      pld_sum <- sapply(apply(pld,2,sum)+log(prior),pldBound)
      pd <- exp(pld_sum)
      res[[w]] <- round(pd/sum(pd),4)
      }
    tab <- data.frame(do.call(rbind,res))
    rownames(tab) <- names(datList)
    colnames(tab) <- 1:length(beta)
    tab
    }
  }
