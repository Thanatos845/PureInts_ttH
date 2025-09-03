{
(* Grams *)
sqrtG1 -> root[v12^2 - 4*mTsq*qsq],
sqrtG2 -> root[v23^2 - 4*mTsq*qsq],
sqrtG3 -> root[(qsq+v23-v45)^2 - 4*mTsq*v45],
sqrtG4 -> root[(qsq+v12-v45)^2 - 4*mTsq*v45],
sqrtG5 -> root[(qsq+v34-v15)^2 - 4*qsq*(mTsq+v34)],
sqrtD5 -> root[qsq^4+(v12 (v15-v23)+v23 v34)^2+2 qsq^3 (v12-v15+v23-v34-v45)+2 (-2 mTsq (v12+v15-v34) (v15-v23-v34)+v23 (v15-v34) v34+v12 (-v15^2+v23 v34+v15 (v23+v34))) v45+(v15-v34)^2 v45^2+qsq^2 (v12^2+v15^2+v23^2-4 v23 v34+v34^2+4 mTsq v45-2 v23 v45+4 v34 v45+v45^2-2 v12 (2 v15-2 v23+v34+v45)+2 v15 (-v23+v34+2 v45))+2 qsq (v12^2 (-v15+v23)-v15^2 v45+v12 (v15^2-2 v15 v23+v23^2+v15 v34-2 v23 v34+(2 mTsq+2 v15-v23+v34) v45)+v15 (-v45^2+v23 (v34+v45))-(v23-v45) (v23 v34-2 mTsq v45-v34 (v34+v45)))],

(* Cayleys *)
sqrtC1 -> root[qsq*(qsq-4*mTsq)],
sqrtC2 -> root[( (qsq+v12)*(qsq+v23) - qsq*v45 )*( (qsq+v12)*(qsq+v23)-(qsq-4*mTsq)*v45 )],

(* other *)
sqrtR1 -> root[(2*qsq+v12+v23)^2 - 4*qsq*v45],
sqrtR2 -> root[(qsq + v23)^2*(qsq + v12 - v34)^2 - 2*(qsq + v23)*(qsq^2 + qsq*(-2*mTsq + v12 - v34) - 2*mTsq*(v12 + v15 - v34))*v45 + qsq*(qsq - 4*mTsq)*v45^2],
sqrtR3 -> root[(qsq + v12)^2*(qsq - v15 + v23)^2 - 2*(qsq + v12)*((qsq - 2*mTsq)*(qsq - v15 + v23) - 2*mTsq*v34)*v45 + qsq*(qsq - 4*mTsq)*v45^2],
sqrtR4 -> root[4*(qsq^6 + mTsq^2*(v12 + v23)^4 + 2*qsq^5*(-4*mTsq + v12 + v23 - 2*v45) + qsq^4*(16*mTsq^2 + v12^2 + 4*v12*v23 + v23^2 - 16*mTsq*(v12 + v23 - v45) - 6*(v12 + v23)*v45 + 6*v45^2) + qsq^2*(24*mTsq^2*(v12 + v23)^2 - 2*mTsq*(v12 + v23)*(v12^2 + 6*v12*v23 + v23^2) + (v12 - v45)^2*(v23 - v45)^2 + 4*mTsq*(v12^2 + 10*v12*v23 + v23^2)*v45 - 8*mTsq*(v12 + v23)*v45^2) + 2*qsq*mTsq*(-(v12*v23*(v12 + v23)^2) + 4*mTsq*(v12 + v23)^3 - (v12 + v23)*(v12^2 - 6*v12*v23 + v23^2)*v45 + (v12^2 - 6*v12*v23 + v23^2)*v45^2) + 2*qsq^3*(16*mTsq^2*(v12 + v23) + (v12 + v23 - 2*v45)*(v12 - v45)*(v23 - v45) + mTsq*(-5*v12^2 - 14*v12*v23 - 5*v23^2 + 12*(v12 + v23)*v45 - 4*v45^2)))],

(* Nested Roots *)
sqrtN1 -> root[qsq*(2*qsq^3 - 2*mTsq*(v12 + v23)^2 + 2*qsq^2*(-4*mTsq + v12 + v23 - 2*v45) + qsq*(v12^2 + v23^2 - 8*mTsq*(v12 + v23) - 2*(v12 + v23)*v45 + 2*v45^2) + sqrtR4)],
sqrtN2 -> sqrtC1*qsq*(v12-v23)*(2*qsq+v12+v23-2*v45)/sqrtN1
}
