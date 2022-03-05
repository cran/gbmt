\name{plot.gbmt}
\alias{plot.gbmt}
\title{Graphics for a group-based multivariate trajectory model}
\description{Visualization of estimated and predicted trajectories.}
\usage{
\method{plot}{gbmt}(x, group=NULL, unit=NULL, x.names=NULL, n.ahead=0, bands=TRUE, conf=0.95,
  observed=TRUE, equal.scale=FALSE, trim=0, ylim=NULL, xlab="", ylab="", titles=NULL,
  add.grid=TRUE, col=NULL, transparency=-1, add.legend=TRUE, pos.legend=c(0,0),
  cex.legend=0.6, mar=c(5.1,4.1,4.1,2.1), ...)
}
\arguments{
  \item{x}{Object of class \code{gbmt}.}
  \item{group}{Numerical value indicating the group for which the estimated trajectories should be displayed. If \code{NULL} (the default), the estimated trajectories for each group will be overlapped. Ignored if \code{unit} is not \code{NULL}.}
  \item{unit}{Character indicating the name of the unit for which estimated trajectories should be displayed. If \code{NULL} (the default), estimated group trajectories are displayed.}
  \item{x.names}{Character including the names of the indicators for which the estimated trajectory should be displayed. If \code{NULL} (the default), estimated trajectories of all indicators are displayed.}
  \item{n.ahead}{Non-negative integer value indicating the number of steps ahead to perform prediction. Default is 0, meaning no prediction.}
  \item{bands}{Logical value indicating whether the prediction bands for should be drawn. Default is \code{TRUE}.}
  \item{conf}{Numerical value indicating the confidence level for the prediction bands. Default is 0.05. Ignored if \code{bands} is \code{FALSE}.}
  \item{observed}{Logical indicating whether observed trajectories should be drawn. Default is \code{TRUE}. Ignored if both \code{group} and \code{unit} are \code{NULL}.}
  \item{equal.scale}{Logical indicating whether indicators should have the same scale across all groups. Default is \code{FALSE}. Ignored if \code{ylim} is not \code{NULL} or if \code{unit} is not \code{NULL}.}
\item{trim}{Numerical value indicating the proportion of extreme values to trim when either \code{equal.scale} is \code{TRUE}. Ignored if \code{observed} is \code{FALSE} or both \code{group} and \code{unit} are \code{NULL}. Default is 0, meaning no trim.}
  \item{ylim}{vector of length 2 indicating the limits of the y-axis, which will be applied to all indicators. If \code{NULL} (the default), it will be determined independently for each indicator based on data, unless \code{equal.scale} is \code{TRUE}.}
  \item{xlab}{label for the x-axis, which will be applied to all indicators. Default is empty string.}
  \item{ylab}{label for the y-axis, which will be applied to all indicators. Default is empty strings.}
  \item{titles}{vector of titles for the indicators. If \code{NULL}, the name of the indicators is used as title.}
  \item{add.grid}{Logical value indicating whether the grid should be added. Default is \code{TRUE}.}
  \item{col}{Character or numerical vector indicating the color of group trajectories. If \code{group} is not \code{NULL}, only the first valid color is considered. If \code{group} is \code{NULL} and there are more than \code{ng} valid colors, only the first \code{ng} valid colors are considered, otherwise valid colors are recycled to achieve a total number equal to \code{ng}. If \code{NULL} (the default), colors of group trajectories will be determined automatically.}
  \item{transparency}{Numerical value between 0 and 100 indicating the trasparency of prediction regions. Value 75 is suggested. If negative, only prediction bands are displayed. Default is -1. Ignored if \code{group} is not \code{NULL} or \code{bands} is \code{FALSE}.}
  \item{add.legend}{Logical value indicating whether the legend for groups should be added. Default is \code{TRUE}.}
  \item{pos.legend}{Numerical vector of length 2 indicating the horizontal-vertical shift of the legend for groups with respect to the position 'topleft'. Default is \code{c(0,0)}. Ignored if \code{group} is not \code{NULL} or \code{add.legend} is \code{FALSE}.}
  \item{cex.legend}{Expansion factor relative to the legend for groups. Default is 0.6. Ignored if \code{group} is not \code{NULL} or \code{add.legend} is \code{FALSE}.}
  \item{mar}{Numerical vector of length 4 indicating the margin size in the order: bottom, left, top, right, which will be applied to all indicators. Default is \code{c(5.1,4.1,4.1,2.1)}.}
  \item{...}{Further graphical parameters.}
}
\value{No return value.}
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

# group trajectories including 3 steps ahead prediction
mar0 <- c(3.1,2.55,3.1,1.2)
plot(m3_2, n.ahead=3, mar=mar0)  ## overlapped groups
plot(m3_2, group=1, n.ahead=3, mar=mar0)  ## group 1
plot(m3_2, group=2, n.ahead=3, mar=mar0)  ## group 2
plot(m3_2, group=3, n.ahead=3, mar=mar0)  ## group 3

# same scale to ease comparisons
plot(m3_2, n.ahead=3, mar=mar0, equal.scale=TRUE)
plot(m3_2, group=1, n.ahead=3, mar=mar0, equal.scale=TRUE, trim=0.05)
plot(m3_2, group=2, n.ahead=3, mar=mar0, equal.scale=TRUE, trim=0.05)
plot(m3_2, group=3, n.ahead=3, mar=mar0, equal.scale=TRUE, trim=0.05)

# overlapped groups with transparency
plot(m3_2, group=1, n.ahead=3, mar=mar0, equal.scale=TRUE, trim=0.05,
  transparency=80)

# trajectories including 3 steps ahead prediction for unit 'Italy'
plot(m3_2, unit="Italy", n.ahead=3, transparency=80)
}