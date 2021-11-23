\name{predict.gbmt}
\alias{predict.gbmt}
\title{Prediction based on a group-based multivariate trajectory model}
\description{Computation of in-sample and/or out-of-sample prediction of trajectories.}
\usage{
\method{predict}{gbmt}(object, unit=NULL, n.ahead=0, bands=TRUE, conf=0.95, in.sample=FALSE, ...)
}
\arguments{
  \item{object}{Object of class \code{gbmt}.}
  \item{unit}{Character indicating the name of the unit for which prediction should be performed. If \code{NULL} (the default), group trajectories are predicted.}
  \item{n.ahead}{Non-negative integer value indicating the number of steps ahead for prediction. If a numerical vector is provided, only the maximum value is considered. If 0 (the default), in-sample prediction is returned.}
  \item{bands}{Logical value indicating whether the prediction bands should be computed.}
  \item{conf}{Numerical value indicating the confidence level for the prediction bands. Default is 0.05. Ignored if \code{bands} is \code{FALSE}.}
  \item{in.sample}{Logical value indicating whether in-sample prediction should be returned along with out-of-sample one. If \code{FALSE} (the default) and \code{n.ahead} is greater than 0, out-of-sample prediction is returned. Ignored if \code{n.ahead} is 0.}
  \item{...}{Further arguments for the generic \code{predict} method.}
}
\value{If \code{unit} is \code{NULL}, a list with one component for each group, including a list with one object of class \code{data.frame} for each indicator. Otherwise, a list with one object of class \code{data.frame} for each indicator. Each of these dataframes has one column containing point predictions if \code{bands}=\code{FALSE}, otherwise three columns containing point predictions and their respective predictive bands.}
%\details{}
\note{If \code{unit} is not \code{NULL}, values are back transformed to the original scales of indicators.}
%\references{}
\seealso{\link{gbmt}.}
\examples{
data(agrisus2)

# names of indicators (just a subset for illustration)
varNames <- c("TFP_2005", "NetCapital_GVA",
  "Income_rur", "Unempl_rur", "GHG_UAA", "GNB_N_UAA")

# model with 2 polynomial degrees and 3 groups
m3_2 <- gbmt(x.names=varNames, unit="Country", time="Year", d=2, ng=3, data=agrisus2, scaling=4)

# 3 steps ahead prediction of group trajectories
predict(m3_2, n.ahead=3)
predict(m3_2, n.ahead=3, in.sample=TRUE)  ## include in-sample prediction

# 3 steps ahead prediction for unit 'Italy'
predict(m3_2, unit="Italy", n.ahead=3)
predict(m3_2, unit="Italy", n.ahead=3, in.sample=TRUE)  ## include in-sample prediction
}
