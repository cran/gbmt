\name{gbmt-package}
\alias{gbmt-package}
\docType{package}
\title{Group-Based Multivariate Trajectory Modeling}
\description{Estimation and analysis of group-based multivariate trajectory models.}
\details{
  \tabular{ll}{
  Package: \tab gbmt\cr
  Type: \tab Package\cr
  Version: \tab 0.1.4\cr
  Date: \tab 2024-12-02\cr
  License: \tab GPL-2
  }
Group-based trajectory modeling is a statistical method to determine groups of units based on the trend of a multivariate time series.
It is a special case of latent class growth curves where the units in the same group have the same trajectory (Nagin, 2005), but it assumes a multivariate polynomial regression on time within each group, instead of a univariate one, to account for multiple indicators (Nagin et al., 2018; Magrini, 2022).
A group-based multivariate trajectory model is estimated through the Expectation-Maximization (EM) algorithm, which allows unbalanced panel and missing values.
The main functions currently implemented in the package are:
\itemize{
\item \link{gbmt}: to estimate a group-based multivariate trajectory model;
\item \link{predict.gbmt}: to perform prediction on trajectories;
\item \link{plot.gbmt}: to display estimated and predicted trajectories;
\item \link{posterior}: to compute posterior probabilities for new units.
}
}
\author{Alessandro Magrini <alessandro.magrini@unifi.it>}
\references{
A. Magrini (2022). Assessment of agricultural sustainability in European Union countries: A group-based multivariate trajectory approach. \emph{AStA Advances in Statistical Analysis}, 106, 673-703. DOI: 10.1007/s10182-022-00437-9

D. S. Nagin, B. L. Jones, V. L. Passos and R. E. Tremblay (2018). Group-based multi-trajectory modeling. \emph{Statistical Methods in Medical Research}, 27(7): 2015-2023. DOI: 10.1177/0962280216673085

D. S. Nagin (2005). Group-based modeling of development. Harvard University Press, Cambridge, US-MA.
}
