library(xtable)
library(KernSmooth)
library(ks)
library(pitchRx)
library(plyr)
library(dplyr)
library(igraph)
library(MASS)
library(alphahull)

## Align data on the outline clockwisely 
my_align<- function(pts){
    cent <- apply(pts, 2, mean)
    pts <- as.matrix(pts)
    temp_upper <- pts[pts[,2] > cent[2],]
    start_pt <- as.vector(temp_upper[which.min(abs(temp_upper[,1] - cent[1])), ])
    temp_left <- pts[pts[,1] <=  cent[1], ]
    temp_right <- pts[pts[,1] > cent[1], ]
    my_angle <- function(vec){
        cos_theta <- (start_pt - cent) %*% (vec - cent)/ 
            (sqrt(sum((start_pt - cent) ^ 2)) * sqrt(sum((vec - cent)^ 2)))
        cos_theta
    }
    temp_right_new <- temp_right[order(apply(temp_right, 1, my_angle), decreasing = TRUE),]
    temp_left_new <- temp_left[order(apply(temp_left, 1, my_angle)), ]
    out <- rbind(temp_right_new, temp_left_new)
    out
}

## Elliptic Fourier method
my_ef <- function(pts, n){
    K <- nrow(pts)
    df <- pts - rbind(pts[K, ], pts[-K,])
    df_x <- df[,1]
    df_y <- df[,2]
    df_t <- sqrt(df_x ^ 2 + df_y ^ 2)
    T  <- sum(df_t)
    t_p <- cumsum(df_t)
    an<- sapply(1 : n, function(n)(T / (2 * n ^ 2 * pi ^ 2)) * sum(df_x / df_t * 
                                   (cos(2 * n * pi * t_p / T) - cos(2 * n * pi * c(0, t_p[-K]) / T))))
    
    bn <- sapply(1 : n, function(n)(T / (2 * n ^ 2 * pi ^ 2)) * sum(df_x / df_t * 
                                    (sin(2 * n * pi * t_p / T) - sin(2 * n * pi * c(0, t_p[-K]) / T))))
    
    cn <- sapply(1 : n, function(n)(T / (2 * n ^ 2 * pi ^ 2)) * sum(df_y / df_t * 
                                    (cos(2 * n * pi * t_p / T) - cos(2 * n * pi * c(0, t_p[-K]) / T))))
    
    dn <- sapply(1 : n, function(n)(T / (2 * n ^ 2 * pi ^ 2)) * sum(df_y / df_t * 
                                    (sin(2 * n * pi * t_p / T) - sin(2 * n * pi * c(0, t_p[-K]) / T))))
    
    xi_p <- sapply(2 : K, function(p){sum(df_x[1 : (p - 1)]) - df_x[p] / df_t[p] * sum(df_t[1 : (p-1)])})
    xi_p <- c(0, xi_p)
    
    delta_p <- sapply(2 : K, function(p){sum(df_y[1 : (p - 1)]) - df_y[p] / df_t[p] * sum(df_t[1 : (p-1)])})
    delta_p <- c(0, delta_p)
    
    a0 <- (1 / T) * sum(pts[,1] * df_t)
    c0 <- (1 / T) * sum(pts[,2] * df_t)

    out <- list(an = an, bn = bn, cn = cn, dn = dn, 
                a0 = a0, c0 = c0, tt = t_p, T = T)
    out
}

my_efourier_i <- function(a0, c0, an, bn, cn, dn, nh, pts){
    theta <- seq(0, 2 * pi, length = nrow(pts) + 1)[-(nrow(pts) + 1)]
    hx <- matrix(NA, nh, nrow(pts))
    hy <- matrix(NA, nh, nrow(pts))
    for (i in 1:nh) {
        hx[i, ] <- an[i] * cos(i * theta) + bn[i] * sin(i * theta)
        hy[i, ] <- cn[i] * cos(i * theta) + dn[i] * sin(i * theta)
    }

    x <- a0 + apply(hx, 2, sum) 
    y <- c0 + apply(hy, 2, sum)
    coo <- cbind(x, y)
    coo
}

## Normalized EF coefficients
## subtract 2 * pi from psi if it's close to 2 * pi
## define a new variable called area
my_efnorm <- function(ef, n){
    a1 <- ef$an[1]
    b1 <- ef$bn[1]
    c1 <- ef$cn[1]
    d1 <- ef$dn[1]
    a0 <- ef$a0
    c0 <- ef$c0
    theta <- (1 / 2) * atan(2 * (a1 * b1 + c1 * d1) / (a1 ^ 2 + c1 ^ 2 - b1 ^ 2 - d1 ^ 2)) %% pi
    a1_star <- a1 * cos(theta) + b1 * sin(theta)
    c1_star <- c1 * cos(theta) + d1 * sin(theta)
    aa1_star <- a1 * cos(theta + pi / 2) + b1 * sin(theta + pi / 2)
    cc1_star <- c1 * cos(theta + pi / 2) + d1 * sin(theta + pi / 2)
    if (a1_star ^ 2 + c1_star ^ 2 < aa1_star ^ 2 + cc1_star ^ 2){
        theta <- theta + pi / 2
        a1_star <- aa1_star
        c1_star <- cc1_star
    }
    psi <- atan(c1_star / a1_star)
    if (a1_star >= 0 & c1_star >= 0){
        psi <- psi
    }
    if(a1_star < 0 & c1_star >= 0){
        psi <- psi %% pi
    }
    if (a1_star < 0 & c1_star < 0){
        psi <- psi + pi
    }
    if (a1_star > 0 & c1_star < 0){
        psi <- psi + 2 * pi
    }
    if (psi >  pi ){
        psi <- psi - 2 * pi
    }
    lambda <- sqrt(a1_star ^ 2 + c1_star ^ 2)
    axis_rt <- matrix(c(cos(psi), sin(psi), -sin(psi), cos(psi)), nrow = 2, byrow = TRUE)
    An <- NULL 
    Bn <- NULL
    Cn <- NULL
    Dn <- NULL
    for (i in 1 : n){
        temp_mat<- (1 / lambda) * axis_rt %*% 
            matrix(c(ef$an[i], ef$bn[i], ef$cn[i], ef$dn[i]), nrow = 2, byrow = TRUE) %*% 
            matrix(c(cos(i * theta), - sin(i * theta), sin(i * theta), cos(i * theta)), 
                   nrow = 2, byrow = TRUE)
        An[i] <- temp_mat[1, 1]
        Bn[i] <- temp_mat[1, 2]
        Cn[i] <- temp_mat[2, 1]
        Dn[i] <- temp_mat[2, 2]
    }
    area <- (lambda ^ 2) * abs(Dn[1]) * pi
    out <- list(An = An, Bn = Bn, Cn = Cn, Dn = Dn, a0 = a0, c0 = c0, psi = psi,
                theta = theta, lambda = lambda, area = area)
    out
}
