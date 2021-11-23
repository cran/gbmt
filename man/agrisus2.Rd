\name{agrisus2}
\alias{agrisus2}
\docType{data}
\title{EU agricultural sustainability data (missing values imputed)}
\description{Data on several indicators covering the economic, social and environmental dimensions of agricultural sustainability for 26 EU countries in the period 2004-2018. Missing values have been imputed.}
\usage{data(agrisus2)}
\format{
  A data.frame with a total of 390 observations on the following 16 variables:
  \describe{
    \item{\code{Country}}{Country name.}
    \item{\code{Country_code}}{Country code.}
    \item{\code{Year}}{Time of measurement (year).}
    \item{\code{Date}}{Time of measurement (date).}
    \item{\code{TFP_2005}}{Total Factor Productivity (TFP) index of agriculture (2005=100). Source: Eurostat.}
    \item{\code{NetCapital_GVA}}{Net capital stocks in agriculture (2015 US dollars) to gross value added of agriculture (2015 US dollars). Source: FAO.}
    \item{\code{Manager_ratio}}{Ratio young/elderly for farm managers (number of managers with less than 35 years by 100 managers with 55 years and over). Source: Eurostat.}
    \item{\code{FactorIncome_paid_2010}}{Real income of agricultural factors per paid annual work unit (index 2010=100). Source: Eurostat.}
    \item{\code{EntrIncome_unpaid_2010}}{Net entrepreneurial income of agriculture per unpaid annual work unit (index 2010=100). Source: Eurostat.}
    \item{\code{Income_rur}}{Median equivalised net income in rural areas (power purchasing standard). Source: Eurostat.}
    \item{\code{Unempl_rur}}{At-risk-of-poverty rate in rural areas (\%). Source: Eurostat.}
    \item{\code{Poverty_rur}}{Unemployment rate in rural areas (\%). Source: Eurostat.}
    \item{\code{RenewProd}}{Production of renewable energy from agriculture (share of total production of renewable energy, \%). Source: Eurostat.}
    \item{\code{Organic_p}}{Area under organic cultivation (share of utilized agricultural area, \%). Source: Eurostat.}
    \item{\code{GHG_UAA}}{Greenhouse gas emissions due to agriculture (million CO2 equivalent grams per hectare of utilized agricultural area). Source: FAO.}
    \item{\code{GNB_UAA}}{Gross nitrogen balance (tonnes of nutrient per hectare of utilized agricultural area). Source: OECD.}
  }
}
\note{This is the dataset employed in Magrini (2021) after the imputation of missing values according to a group-based multivariate trajectory model with three groups and three polynomial degrees.}
\references{
A. Magrini (2021). Assessment of agricultural sustainability in European Union countries: A group-based multivariate trajectory approach. To be appeared on \emph{Advances in Statistical Analysis}.
}
\seealso{\link{agrisus}}