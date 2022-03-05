\name{agrisus}
\alias{agrisus}
\docType{data}
\title{EU agricultural sustainability data}
\description{Data on several indicators covering the economic, social and environmental dimensions of agricultural sustainability for 26 EU countries in the period 2004-2018.}
\usage{data(agrisus)}
\format{
  A data.frame with a total of 390 observations on the following 16 variables:
  \describe{
    \item{\code{Country}}{Country name.}
    \item{\code{Country_code}}{Country code.}
    \item{\code{Year}}{Time of measurement (year).}
    \item{\code{Date}}{Time of measurement (date).}
    \item{\code{TFP_2005}}{Total Factor Productivity (TFP) index of agriculture (2005=100). Source: CMEF.}
    \item{\code{NetCapital_GVA}}{Net capital stocks in agriculture (2015 US dollars) to gross value added of agriculture (2015 US dollars). Source: Faostat.}
    \item{\code{Manager_ratio}}{Ratio young/elderly for farm managers (number of managers with less than 35 years by 100 managers with 55 years and over). Source: CMEF.}
    \item{\code{FactorIncome_paid_2010}}{Real income of agricultural factors per paid annual work unit (index 2010=100). Source: Eurostat.}
    \item{\code{EntrIncome_unpaid_2010}}{Net entrepreneurial income of agriculture per unpaid annual work unit (index 2010=100). Source: Eurostat.}
    \item{\code{Income_rur}}{Median equivalised net income in rural areas (power purchasing standard). Source: Eurostat.}
    \item{\code{Unempl_rur}}{At-risk-of-poverty rate in rural areas (\%). Source: Eurostat.}
    \item{\code{Poverty_rur}}{Unemployment rate in rural areas (\%). Source: Eurostat.}
    \item{\code{RenewProd}}{Production of renewable energy from agriculture (share of total production of renewable energy, \%). Source: CMEF.}
    \item{\code{Organic_p}}{Area under organic cultivation (share of utilized agricultural area, \%). Source: Faostat.}
    \item{\code{GHG_UAA}}{Greenhouse gas emissions due to agriculture (million CO2 equivalent grams per hectare of utilized agricultural area). Source: Faostat.}
    \item{\code{GNB_UAA}}{Gross nitrogen balance (tonnes of nutrient per hectare of utilized agricultural area). Source: Eurostat.}
  }
}
\note{This is the dataset employed in Magrini (2022).}
\references{
European Commission (2022). Eurostat database. https://ec.europa.eu/eurostat/data/database

European Commission (2020). Common Monitoring and Evaluation Framework (CMEF) for the CAP 2014-2020. https://agridata.ec.europa.eu/extensions/DataPortal/cmef_indicators.html

Food and Agriculture Organization (2022). FAOSTAT statistical database. https://www.fao.org/faostat/en/#home

A. Magrini (2022). Assessment of agricultural sustainability in European Union countries: A group-based multivariate trajectory approach. \emph{Advances in Statistical Analysis}, published online: March 2022. DOI: 10.1007/s10182-022-00437-9
}
\seealso{\link{agrisus2}}