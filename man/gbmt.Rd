\name{gbmt}
\alias{gbmt}
\title{Estimation of a group-based multivariate trajectory model}
\description{Estimation of a group-based multivariate trajectory model through the Expectation-Maximization (EM) algorithm. Missing values are allowed and the panel may be unbalanced.}
\usage{gbmt(x.names, unit, time, ng=1, d=2, data, scaling=2, pruning=TRUE, delete.empty=FALSE,
  nstart=NULL, tol=1e-4, maxit=1000, quiet=FALSE)}
\arguments{
  \item{x.names}{Character vector including the names of the indicators.}
  \item{unit}{Character indicating the name of the variable identifying the units.}
  \item{time}{Character indicating the name of the variable identifying the time points. There must be at least two time points for each unit.}
  \item{ng}{Positive integer value indicating the number of groups to create. Cannot be greater than half the number of units. Default is 1.}
  \item{d}{Positive integer value indicating the polynomial degree of group trajectories. Cannot be greater than the minimum number of time points across all units minus 1. Default is 2.}
  \item{data}{Object of class \code{data.frame} containing the variables indicated in arguments \code{x.names}, \code{unit} and \code{time}. The variable indicated in argument \code{unit} must be of type 'character' or 'factor' and cannot contain missing values. The variable indicated in argument \code{time} must be of type 'numeric' or 'Date' and cannot contain missing values. Variables indicated in argument \code{x.names} must be of type 'numeric' and may contain missing values. Variables indicated in argument \code{x.names} which are completely missing or not present in \code{data} will be ignored. The time points may differ across units (unbalanced panel) but they must be unique within units.}
  \item{scaling}{Normalisation method, that should be indicated as: 0 (no normalisation), 1 (centering), 2 (standardization), 3 (ratio to the mean) and 4 (logarithmic ratio to the mean). Default is 2 (standardization). See 'Details'.}
  \item{pruning}{Logical value indicating whether non-significant polynomial terms should be dropped. Default is \code{TRUE}. See 'Details'.}
  \item{delete.empty}{Logical value indicating whether empty groups should be deleted. Default is \code{FALSE}.}
  \item{nstart}{Positive integer value indicating the number of random restarts of the EM algorithm. If \code{NULL} (the default), the EM algorithm is started from the solution of a hierarchical cluster with Ward's linkage.}
  \item{tol}{Positive value indicating the tolerance of the EM algorithm. Default is 1e-4.}
  \item{maxit}{Positive integer value indicating the maximum number of iterations of the EM algorithm. Default is 1000.}
  \item{quiet}{Logical value indicating whether prompt messages should be suppressed. Default is \code{FALSE}.}
  }
\value{An object of class \code{gbmt}, including the following components:
  \item{\code{call}: }{list including details on the call.}
  \item{\code{prior}: }{vector including the estimated prior probabilities.}
  \item{\code{beta}: }{list of matrices, one for each group, including the estimated regression coefficients.}
  \item{\code{Sigma}: }{list of matrices, one for each group, including the estimated covariance matrix of the indicators.}
  \item{\code{posterior}: }{matrix including posterior probabilities.}
  \item{\code{Xmat}: }{the model matrix employed for each indicator in each group.}
  \item{\code{fitted}: }{list of matrices, one for each group, including the estimated group trajectories.}
  \item{\code{reg}: }{list of objects of class \code{lm}, one for each group and each indicator, including the fitted regressions.}
  \item{\code{assign}: }{vector indicating the assignement of the units to the groups.}
  \item{\code{assign.list}: }{list indicating the assignement of the units to the groups.}
  \item{\code{logLik}: }{log-likelihood of the model.}
  \item{\code{npar}: }{total number of free parameters in the model.}
  \item{\code{ic}: }{information criteria for the model (see Magrini, 2022 for details.}
  \item{\code{appa}: }{average posterior probability of assignments (APPA) for the model.}
  \item{\code{data.orig}: }{data provided to argument \code{data}.}
  \item{\code{data.scaled}: }{data after normalization.}
  \item{\code{data.imputed}: }{data after imputation of missing values, equal to \code{data.orig} if there are no missing data.}
  \item{\code{em}: }{matrix with one row for each run of the EM algorithm, including log-likelihood, number of iterations and convergence status (1=yes, 0=no).}
  }
\details{Let \eqn{Y_1,\ldots,Y_k,\ldots,Y_K} be the considered indicators and \eqn{\mbox{y}_{i,t}=(y_{i,t,1},\ldots,y_{i,t,k},\ldots,y_{i,t,K})'} denote their observation on unit \eqn{i} (\eqn{i=1,\ldots,n}) at time \eqn{t} (\eqn{t=1,\ldots,T}).
Also, let \eqn{\bar{y}_{i,k}} and \eqn{s_{i,k}} be, respectively, sample mean and sample standard deviation of indicator \eqn{Y_k} for unit \eqn{i} across the whole period of observation.
Each indicator is normalized within units according to one among the following normalisation methods:

0) no normalisation:
\deqn{y^*_{i,t,k}=y_{i,t,k}}

1) centering:
\deqn{y^*_{i,t,k}=y_{i,t,k}-\bar{y}_{i,k}}

2) standardization:
\deqn{y^*_{i,t,k}=\frac{y_{i,t,k}-\bar{y}_{i,k}}{s_{i,k}}}

3) ratio to the mean:
\deqn{y^*_{i,t,k}=\frac{y_{i,t,k}}{\bar{y}_{i,k}}}

4) logarithmic ratio to the mean:
\deqn{y^*_{i,t,k}=\log\left(\frac{y_{i,t,k}}{\bar{y}_{i,k}}\right)\approx\frac{y_{i,t,k}-\bar{y}_{i,k}}{\bar{y}_{i,k}}}

Normalisation is required if the trajectories have different levels across units. When indicators have different scales of measurement, standardization is needed to compare the measurements of different indicators. Ratio to the mean and logaritmic ratio to the mean allow comparisons among different indicators as well, but they can be applied only in case of strictly positive measurements.

Denote the hypothesized groups as \eqn{j=1,\ldots,J} and let \eqn{G_i} be a latent variable taking value \eqn{j} if unit \eqn{i} belongs to group \eqn{j}.
A group-based multivariate trajectory model with polynomial degree \eqn{d} is defined as:
\deqn{\mbox{y}^*_{i,t}\mid G_i=j\sim\mbox{MVN}\left(\mu_j,\Sigma_j\right)\hspace{.9cm}j=1,\ldots,J}
\deqn{\mu_j=\mbox{B}_j'\left(1,t,t^2,\ldots,t^d\right)'}
where \eqn{\mbox{B}_j} is the \eqn{(d+1)\times K} matrix of regression coefficients in group \eqn{j}, and \eqn{\Sigma_j} is the \eqn{K \times K} covariance matrix of the indicators in group \eqn{j}.
The likelihood of the model is:
\deqn{\mathcal{L}(\mbox{B}_1,\ldots,\mbox{B}_J,\Sigma_1,\ldots,\Sigma_J,\pi_1,\ldots,\pi_J)=\prod_{i=1}^n\left[\sum_{j=1}^J\pi_j \prod_{t=1}^T\phi(\mbox{y}^*_{i,t}\mid \mbox{B}_j,\Sigma_j)\right]}
where \eqn{\phi(\mbox{y}^*_{i,t}\mid \mbox{B}_j,\Sigma_j)} is the multivariate Normal density of \eqn{\mbox{y}^*_{i,t}} in group \eqn{j}, and \eqn{\pi_j} is the prior probability of group \eqn{j}.
The posterior probability of group \eqn{j} for unit \eqn{i} is computed as:
\deqn{\mbox{Pr}(G_i=j\mid \mbox{y}^*_i)\equiv\pi_{i,j}=\frac{\widehat{\pi}_j \prod_{t=1}^{T}\phi(\mbox{y}^*_{i,t}\mid \widehat{\mbox{B}}_j,\widehat{\Sigma}_j)}{\sum_{j=1}^J\widehat{\pi}_j \prod_{t=1}^{T}\phi(\mbox{y}^*_{i,t}\mid \widehat{\mbox{B}}_j,\widehat{\Sigma}_j)}}
where the hat symbol above a parameter denotes the estimated value for that parameter.
See the vignette of the package and Magrini (2022) for details on maximum likelihood estimation through the EM algorithm.

S3 methods available for class \code{gbmt} include:
\itemize{
  \item \code{print}: to see the estimated regression coefficients for each group;
  \item \code{summary}: to obtain the summary of the linear regressions (a list with one component for each group and each indicator);
  \item \code{plot}: to display estimated and predicted trajectories. See \link{plot.gbmt} for details;
  \item \code{coef}: to see the estimated coefficients (a list with one component for each group);
  \item \code{fitted}: to obtain the fitted values, equating to the estimated group trajectories (a list with one component for each group);
  \item \code{residuals}: to obtain the residuals (a list with one component for each group);
  \item \code{predict}: to perform prediction on trajectories. See \link{predict.gbmt} for details.
  \item \code{logLik}: to get the log likelihood;
  \item \code{AIC}, \code{extractAIC}: to get the Akaike information criterion;
  \item \code{BIC}: to get the Bayesian information criterion.
  }
}
%\note{}
\references{
A. Magrini (2022). Assessment of agricultural sustainability in European Union countries: A group-based multivariate trajectory approach. \emph{AStA Advances in Statistical Analysis}, 106, 673-703. DOI: 10.1007/s10182-022-00437-9
}
\seealso{\link{plot.gbmt}; \link{predict.gbmt}.}
\examples{
data(agrisus2)

# names of indicators (just a subset for illustration)
varNames <- c("TFP_2005", "NetCapital_GVA",
  "Income_rur", "Unempl_rur", "GHG_UAA", "GNB_N_UAA")

# model with 2 degrees and 3 groups using the imputed dataset
# - log ratio to the mean is used as normalisation (scaling=4), thus values
#   represent relative changes with respect to country averages (see Magrini, 2022)
# - by default, standardization (scaling=2) is used, which indicates the number
#   of standard deviations away from the country averages.
m3_2 <- gbmt(x.names=varNames, unit="Country", time="Year", d=2, ng=3, data=agrisus2, scaling=4)

\dontrun{
# same model with multiple random restarts
m3_2r <- gbmt(x.names=varNames, unit="Country", time="Year", d=2, ng=3, data=agrisus2,
  scaling=4, nstart=10)}

# resulting groups
m3_2$assign.list

# estimated group trajectories
m3_2$fitted

# summary of regressions by group
summary(m3_2)

# fit a model with 4 groups
m4_2 <- gbmt(x.names=varNames, unit="Country", time="Year", d=2, ng=4, data=agrisus2,
  scaling=4)
rbind(m3_2$ic, m4_2$ic)  ## comparison

\dontrun{
## model for children's achievement tests: 5 groups, 2 polynomial degrees
#   - scaling=1 (centering): values are interpreted as absolute differences
#     from the child average
#   - scaling=2 (standardization): values are interpreted as standard deviations
#     away from the child average
data(achievement)
m_achiev <- gbmt(x.names=c("speaking","reading","writing","math"),
  unit="id", time="time", d=2, ng=5, scaling=2, data=achievement)}
}
