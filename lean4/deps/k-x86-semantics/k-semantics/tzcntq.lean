def tzcntq1 : instruction :=
  definst "tzcntq" $ do
    pattern fun (v_2507 : reg (bv 64)) (v_2508 : reg (bv 64)) => do
      v_4459 <- getRegister v_2507;
      v_4651 <- eval (mux (eq (extract v_4459 63 64) (expression.bv_nat 1 1)) (expression.bv_nat 64 0) (mux (eq (extract v_4459 62 63) (expression.bv_nat 1 1)) (expression.bv_nat 64 1) (mux (eq (extract v_4459 61 62) (expression.bv_nat 1 1)) (expression.bv_nat 64 2) (mux (eq (extract v_4459 60 61) (expression.bv_nat 1 1)) (expression.bv_nat 64 3) (mux (eq (extract v_4459 59 60) (expression.bv_nat 1 1)) (expression.bv_nat 64 4) (mux (eq (extract v_4459 58 59) (expression.bv_nat 1 1)) (expression.bv_nat 64 5) (mux (eq (extract v_4459 57 58) (expression.bv_nat 1 1)) (expression.bv_nat 64 6) (mux (eq (extract v_4459 56 57) (expression.bv_nat 1 1)) (expression.bv_nat 64 7) (mux (eq (extract v_4459 55 56) (expression.bv_nat 1 1)) (expression.bv_nat 64 8) (mux (eq (extract v_4459 54 55) (expression.bv_nat 1 1)) (expression.bv_nat 64 9) (mux (eq (extract v_4459 53 54) (expression.bv_nat 1 1)) (expression.bv_nat 64 10) (mux (eq (extract v_4459 52 53) (expression.bv_nat 1 1)) (expression.bv_nat 64 11) (mux (eq (extract v_4459 51 52) (expression.bv_nat 1 1)) (expression.bv_nat 64 12) (mux (eq (extract v_4459 50 51) (expression.bv_nat 1 1)) (expression.bv_nat 64 13) (mux (eq (extract v_4459 49 50) (expression.bv_nat 1 1)) (expression.bv_nat 64 14) (mux (eq (extract v_4459 48 49) (expression.bv_nat 1 1)) (expression.bv_nat 64 15) (mux (eq (extract v_4459 47 48) (expression.bv_nat 1 1)) (expression.bv_nat 64 16) (mux (eq (extract v_4459 46 47) (expression.bv_nat 1 1)) (expression.bv_nat 64 17) (mux (eq (extract v_4459 45 46) (expression.bv_nat 1 1)) (expression.bv_nat 64 18) (mux (eq (extract v_4459 44 45) (expression.bv_nat 1 1)) (expression.bv_nat 64 19) (mux (eq (extract v_4459 43 44) (expression.bv_nat 1 1)) (expression.bv_nat 64 20) (mux (eq (extract v_4459 42 43) (expression.bv_nat 1 1)) (expression.bv_nat 64 21) (mux (eq (extract v_4459 41 42) (expression.bv_nat 1 1)) (expression.bv_nat 64 22) (mux (eq (extract v_4459 40 41) (expression.bv_nat 1 1)) (expression.bv_nat 64 23) (mux (eq (extract v_4459 39 40) (expression.bv_nat 1 1)) (expression.bv_nat 64 24) (mux (eq (extract v_4459 38 39) (expression.bv_nat 1 1)) (expression.bv_nat 64 25) (mux (eq (extract v_4459 37 38) (expression.bv_nat 1 1)) (expression.bv_nat 64 26) (mux (eq (extract v_4459 36 37) (expression.bv_nat 1 1)) (expression.bv_nat 64 27) (mux (eq (extract v_4459 35 36) (expression.bv_nat 1 1)) (expression.bv_nat 64 28) (mux (eq (extract v_4459 34 35) (expression.bv_nat 1 1)) (expression.bv_nat 64 29) (mux (eq (extract v_4459 33 34) (expression.bv_nat 1 1)) (expression.bv_nat 64 30) (mux (eq (extract v_4459 32 33) (expression.bv_nat 1 1)) (expression.bv_nat 64 31) (mux (eq (extract v_4459 31 32) (expression.bv_nat 1 1)) (expression.bv_nat 64 32) (mux (eq (extract v_4459 30 31) (expression.bv_nat 1 1)) (expression.bv_nat 64 33) (mux (eq (extract v_4459 29 30) (expression.bv_nat 1 1)) (expression.bv_nat 64 34) (mux (eq (extract v_4459 28 29) (expression.bv_nat 1 1)) (expression.bv_nat 64 35) (mux (eq (extract v_4459 27 28) (expression.bv_nat 1 1)) (expression.bv_nat 64 36) (mux (eq (extract v_4459 26 27) (expression.bv_nat 1 1)) (expression.bv_nat 64 37) (mux (eq (extract v_4459 25 26) (expression.bv_nat 1 1)) (expression.bv_nat 64 38) (mux (eq (extract v_4459 24 25) (expression.bv_nat 1 1)) (expression.bv_nat 64 39) (mux (eq (extract v_4459 23 24) (expression.bv_nat 1 1)) (expression.bv_nat 64 40) (mux (eq (extract v_4459 22 23) (expression.bv_nat 1 1)) (expression.bv_nat 64 41) (mux (eq (extract v_4459 21 22) (expression.bv_nat 1 1)) (expression.bv_nat 64 42) (mux (eq (extract v_4459 20 21) (expression.bv_nat 1 1)) (expression.bv_nat 64 43) (mux (eq (extract v_4459 19 20) (expression.bv_nat 1 1)) (expression.bv_nat 64 44) (mux (eq (extract v_4459 18 19) (expression.bv_nat 1 1)) (expression.bv_nat 64 45) (mux (eq (extract v_4459 17 18) (expression.bv_nat 1 1)) (expression.bv_nat 64 46) (mux (eq (extract v_4459 16 17) (expression.bv_nat 1 1)) (expression.bv_nat 64 47) (mux (eq (extract v_4459 15 16) (expression.bv_nat 1 1)) (expression.bv_nat 64 48) (mux (eq (extract v_4459 14 15) (expression.bv_nat 1 1)) (expression.bv_nat 64 49) (mux (eq (extract v_4459 13 14) (expression.bv_nat 1 1)) (expression.bv_nat 64 50) (mux (eq (extract v_4459 12 13) (expression.bv_nat 1 1)) (expression.bv_nat 64 51) (mux (eq (extract v_4459 11 12) (expression.bv_nat 1 1)) (expression.bv_nat 64 52) (mux (eq (extract v_4459 10 11) (expression.bv_nat 1 1)) (expression.bv_nat 64 53) (mux (eq (extract v_4459 9 10) (expression.bv_nat 1 1)) (expression.bv_nat 64 54) (mux (eq (extract v_4459 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 64 55) (mux (eq (extract v_4459 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 64 56) (mux (eq (extract v_4459 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 64 57) (mux (eq (extract v_4459 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 64 58) (mux (eq (extract v_4459 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 64 59) (mux (eq (extract v_4459 3 4) (expression.bv_nat 1 1)) (expression.bv_nat 64 60) (mux (eq (extract v_4459 2 3) (expression.bv_nat 1 1)) (expression.bv_nat 64 61) (mux (eq (extract v_4459 1 2) (expression.bv_nat 1 1)) (expression.bv_nat 64 62) (mux (eq (extract v_4459 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 64 63) (expression.bv_nat 64 64)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
      setRegister (lhs.of_reg v_2508) v_4651;
      setRegister of undef;
      setRegister pf undef;
      setRegister zf (zeroFlag v_4651);
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (mux (eq v_4651 (expression.bv_nat 64 64)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2503 : Mem) (v_2504 : reg (bv 64)) => do
      v_10038 <- evaluateAddress v_2503;
      v_10039 <- load v_10038 8;
      v_10231 <- eval (mux (eq (extract v_10039 63 64) (expression.bv_nat 1 1)) (expression.bv_nat 64 0) (mux (eq (extract v_10039 62 63) (expression.bv_nat 1 1)) (expression.bv_nat 64 1) (mux (eq (extract v_10039 61 62) (expression.bv_nat 1 1)) (expression.bv_nat 64 2) (mux (eq (extract v_10039 60 61) (expression.bv_nat 1 1)) (expression.bv_nat 64 3) (mux (eq (extract v_10039 59 60) (expression.bv_nat 1 1)) (expression.bv_nat 64 4) (mux (eq (extract v_10039 58 59) (expression.bv_nat 1 1)) (expression.bv_nat 64 5) (mux (eq (extract v_10039 57 58) (expression.bv_nat 1 1)) (expression.bv_nat 64 6) (mux (eq (extract v_10039 56 57) (expression.bv_nat 1 1)) (expression.bv_nat 64 7) (mux (eq (extract v_10039 55 56) (expression.bv_nat 1 1)) (expression.bv_nat 64 8) (mux (eq (extract v_10039 54 55) (expression.bv_nat 1 1)) (expression.bv_nat 64 9) (mux (eq (extract v_10039 53 54) (expression.bv_nat 1 1)) (expression.bv_nat 64 10) (mux (eq (extract v_10039 52 53) (expression.bv_nat 1 1)) (expression.bv_nat 64 11) (mux (eq (extract v_10039 51 52) (expression.bv_nat 1 1)) (expression.bv_nat 64 12) (mux (eq (extract v_10039 50 51) (expression.bv_nat 1 1)) (expression.bv_nat 64 13) (mux (eq (extract v_10039 49 50) (expression.bv_nat 1 1)) (expression.bv_nat 64 14) (mux (eq (extract v_10039 48 49) (expression.bv_nat 1 1)) (expression.bv_nat 64 15) (mux (eq (extract v_10039 47 48) (expression.bv_nat 1 1)) (expression.bv_nat 64 16) (mux (eq (extract v_10039 46 47) (expression.bv_nat 1 1)) (expression.bv_nat 64 17) (mux (eq (extract v_10039 45 46) (expression.bv_nat 1 1)) (expression.bv_nat 64 18) (mux (eq (extract v_10039 44 45) (expression.bv_nat 1 1)) (expression.bv_nat 64 19) (mux (eq (extract v_10039 43 44) (expression.bv_nat 1 1)) (expression.bv_nat 64 20) (mux (eq (extract v_10039 42 43) (expression.bv_nat 1 1)) (expression.bv_nat 64 21) (mux (eq (extract v_10039 41 42) (expression.bv_nat 1 1)) (expression.bv_nat 64 22) (mux (eq (extract v_10039 40 41) (expression.bv_nat 1 1)) (expression.bv_nat 64 23) (mux (eq (extract v_10039 39 40) (expression.bv_nat 1 1)) (expression.bv_nat 64 24) (mux (eq (extract v_10039 38 39) (expression.bv_nat 1 1)) (expression.bv_nat 64 25) (mux (eq (extract v_10039 37 38) (expression.bv_nat 1 1)) (expression.bv_nat 64 26) (mux (eq (extract v_10039 36 37) (expression.bv_nat 1 1)) (expression.bv_nat 64 27) (mux (eq (extract v_10039 35 36) (expression.bv_nat 1 1)) (expression.bv_nat 64 28) (mux (eq (extract v_10039 34 35) (expression.bv_nat 1 1)) (expression.bv_nat 64 29) (mux (eq (extract v_10039 33 34) (expression.bv_nat 1 1)) (expression.bv_nat 64 30) (mux (eq (extract v_10039 32 33) (expression.bv_nat 1 1)) (expression.bv_nat 64 31) (mux (eq (extract v_10039 31 32) (expression.bv_nat 1 1)) (expression.bv_nat 64 32) (mux (eq (extract v_10039 30 31) (expression.bv_nat 1 1)) (expression.bv_nat 64 33) (mux (eq (extract v_10039 29 30) (expression.bv_nat 1 1)) (expression.bv_nat 64 34) (mux (eq (extract v_10039 28 29) (expression.bv_nat 1 1)) (expression.bv_nat 64 35) (mux (eq (extract v_10039 27 28) (expression.bv_nat 1 1)) (expression.bv_nat 64 36) (mux (eq (extract v_10039 26 27) (expression.bv_nat 1 1)) (expression.bv_nat 64 37) (mux (eq (extract v_10039 25 26) (expression.bv_nat 1 1)) (expression.bv_nat 64 38) (mux (eq (extract v_10039 24 25) (expression.bv_nat 1 1)) (expression.bv_nat 64 39) (mux (eq (extract v_10039 23 24) (expression.bv_nat 1 1)) (expression.bv_nat 64 40) (mux (eq (extract v_10039 22 23) (expression.bv_nat 1 1)) (expression.bv_nat 64 41) (mux (eq (extract v_10039 21 22) (expression.bv_nat 1 1)) (expression.bv_nat 64 42) (mux (eq (extract v_10039 20 21) (expression.bv_nat 1 1)) (expression.bv_nat 64 43) (mux (eq (extract v_10039 19 20) (expression.bv_nat 1 1)) (expression.bv_nat 64 44) (mux (eq (extract v_10039 18 19) (expression.bv_nat 1 1)) (expression.bv_nat 64 45) (mux (eq (extract v_10039 17 18) (expression.bv_nat 1 1)) (expression.bv_nat 64 46) (mux (eq (extract v_10039 16 17) (expression.bv_nat 1 1)) (expression.bv_nat 64 47) (mux (eq (extract v_10039 15 16) (expression.bv_nat 1 1)) (expression.bv_nat 64 48) (mux (eq (extract v_10039 14 15) (expression.bv_nat 1 1)) (expression.bv_nat 64 49) (mux (eq (extract v_10039 13 14) (expression.bv_nat 1 1)) (expression.bv_nat 64 50) (mux (eq (extract v_10039 12 13) (expression.bv_nat 1 1)) (expression.bv_nat 64 51) (mux (eq (extract v_10039 11 12) (expression.bv_nat 1 1)) (expression.bv_nat 64 52) (mux (eq (extract v_10039 10 11) (expression.bv_nat 1 1)) (expression.bv_nat 64 53) (mux (eq (extract v_10039 9 10) (expression.bv_nat 1 1)) (expression.bv_nat 64 54) (mux (eq (extract v_10039 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 64 55) (mux (eq (extract v_10039 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 64 56) (mux (eq (extract v_10039 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 64 57) (mux (eq (extract v_10039 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 64 58) (mux (eq (extract v_10039 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 64 59) (mux (eq (extract v_10039 3 4) (expression.bv_nat 1 1)) (expression.bv_nat 64 60) (mux (eq (extract v_10039 2 3) (expression.bv_nat 1 1)) (expression.bv_nat 64 61) (mux (eq (extract v_10039 1 2) (expression.bv_nat 1 1)) (expression.bv_nat 64 62) (mux (eq (extract v_10039 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 64 63) (expression.bv_nat 64 64)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
      setRegister (lhs.of_reg v_2504) v_10231;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_10231);
      setRegister sf undef;
      setRegister cf (mux (eq v_10231 (expression.bv_nat 64 64)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
