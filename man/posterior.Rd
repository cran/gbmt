\name{posterior}
\alias{posterior}
\title{Posterior probabilities based on a group-based multivariate trajectory model}
\description{Computation of posterior probabilities for new units.}
\usage{posterior(x, newdata=NULL)}
\arguments{
  \item{x}{Object of class \code{gbmt}.}
  \item{newdata}{Object of class \code{data.frame} containing the multivariate time series of the indicators for the new units. If \code{NULL} (the default), posterior probabilities of the sample units are returned. If \code{newdata} is not \code{NULL}, it must include the variable identifying the time points. If \code{newdata} does not include the variable identifying the units, it is assumed that all observations refer to the same unit.}
}
\value{An object of class \code{data.frame} with one entry for each unit, containing the posterior probability of each group for that unit.}
%\details{}
\note{Data in \code{newdata} must be expressed on the original scale of the indicators. Normalisation is applied internally.}
%\references{}
\seealso{\link{gbmt}.}
\examples{
data(agrisus2)

# names of indicators (just a subset for illustration)
varNames <- c("TFP_2005", "NetCapital_GVA",
  "Income_rur", "Unempl_rur", "GHG_UAA", "GNB_N_UAA")

# model with 2 polynomial degrees and 3 groups
m3_2 <- gbmt(x.names=varNames, unit="Country", time="Year", d=2, ng=3, data=agrisus2, scaling=4)

# pretend that 'Italy' is a new unit
posterior(m3_2, newdata=agrisus2[which(agrisus2$Country=="Italy"),])

# consider only the last 3 years
posterior(m3_2, newdata=
  agrisus2[which(agrisus2$Country=="Italy"&agrisus2$Year>=2016),]
  )

# provide more than one new unit
posterior(m3_2, newdata=
  agrisus2[which(agrisus2$Country\%in\%c("Italy","Austria","Greece")),]
  )
}
