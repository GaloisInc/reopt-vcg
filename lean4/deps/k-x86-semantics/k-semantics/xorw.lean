def xorw1 : instruction :=
  definst "xorw" $ do
    pattern fun (v_2835 : imm int) ax => do
      v_5255 <- getRegister rax;
      v_5257 <- eval (handleImmediateWithSignExtend v_2835 16 16);
      v_5261 <- eval (bv_xor (extract v_5255 48 64) v_5257);
      setRegister rax (concat (extract v_5255 0 48) v_5261);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_5255 63 64) (extract v_5257 15 16)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_5255 62 63) (extract v_5257 14 15)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5255 61 62) (extract v_5257 13 14)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5255 60 61) (extract v_5257 12 13)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5255 59 60) (extract v_5257 11 12)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5255 58 59) (extract v_5257 10 11)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5255 57 58) (extract v_5257 9 10)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5255 56 57) (extract v_5257 8 9)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_5261 (expression.bv_nat 16 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister sf (bv_xor (extract v_5255 48 49) (extract v_5257 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2847 : imm int) (v_2848 : reg (bv 16)) => do
      v_5329 <- getRegister v_2848;
      v_5331 <- eval (handleImmediateWithSignExtend v_2847 16 16);
      v_5334 <- eval (bv_xor v_5329 v_5331);
      setRegister (lhs.of_reg v_2848) v_5334;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_5329 15 16) (extract v_5331 15 16)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_5329 14 15) (extract v_5331 14 15)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5329 13 14) (extract v_5331 13 14)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5329 12 13) (extract v_5331 12 13)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5329 11 12) (extract v_5331 11 12)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5329 10 11) (extract v_5331 10 11)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5329 9 10) (extract v_5331 9 10)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5329 8 9) (extract v_5331 8 9)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (mux (eq v_5334 (expression.bv_nat 16 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (bv_xor (extract v_5329 0 1) (extract v_5331 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2856 : reg (bv 16)) (v_2857 : reg (bv 16)) => do
      v_5396 <- getRegister v_2857;
      v_5398 <- getRegister v_2856;
      v_5401 <- eval (bv_xor v_5396 v_5398);
      setRegister (lhs.of_reg v_2857) v_5401;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_5396 15 16) (extract v_5398 15 16)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_5396 14 15) (extract v_5398 14 15)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5396 13 14) (extract v_5398 13 14)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5396 12 13) (extract v_5398 12 13)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5396 11 12) (extract v_5398 11 12)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5396 10 11) (extract v_5398 10 11)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5396 9 10) (extract v_5398 9 10)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5396 8 9) (extract v_5398 8 9)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (mux (eq v_5401 (expression.bv_nat 16 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (bv_xor (extract v_5396 0 1) (extract v_5398 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2852 : Mem) (v_2853 : reg (bv 16)) => do
      v_7324 <- getRegister v_2853;
      v_7326 <- evaluateAddress v_2852;
      v_7327 <- load v_7326 2;
      v_7330 <- eval (bv_xor v_7324 v_7327);
      setRegister (lhs.of_reg v_2853) v_7330;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_7324 15 16) (extract v_7327 15 16)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_7324 14 15) (extract v_7327 14 15)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7324 13 14) (extract v_7327 13 14)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7324 12 13) (extract v_7327 12 13)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7324 11 12) (extract v_7327 11 12)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7324 10 11) (extract v_7327 10 11)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7324 9 10) (extract v_7327 9 10)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7324 8 9) (extract v_7327 8 9)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_7330 (expression.bv_nat 16 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister sf (bv_xor (extract v_7324 0 1) (extract v_7327 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2840 : imm int) (v_2839 : Mem) => do
      v_8044 <- evaluateAddress v_2839;
      v_8045 <- load v_8044 2;
      v_8046 <- eval (handleImmediateWithSignExtend v_2840 16 16);
      v_8047 <- eval (bv_xor v_8045 v_8046);
      store v_8044 v_8047 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_8045 15 16) (extract v_8046 15 16)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_8045 14 15) (extract v_8046 14 15)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8045 13 14) (extract v_8046 13 14)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8045 12 13) (extract v_8046 12 13)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8045 11 12) (extract v_8046 11 12)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8045 10 11) (extract v_8046 10 11)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8045 9 10) (extract v_8046 9 10)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8045 8 9) (extract v_8046 8 9)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (mux (eq v_8047 (expression.bv_nat 16 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (bv_xor (extract v_8045 0 1) (extract v_8046 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2844 : reg (bv 16)) (v_2843 : Mem) => do
      v_8108 <- evaluateAddress v_2843;
      v_8109 <- load v_8108 2;
      v_8110 <- getRegister v_2844;
      v_8111 <- eval (bv_xor v_8109 v_8110);
      store v_8108 v_8111 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_8109 15 16) (extract v_8110 15 16)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_8109 14 15) (extract v_8110 14 15)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8109 13 14) (extract v_8110 13 14)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8109 12 13) (extract v_8110 12 13)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8109 11 12) (extract v_8110 11 12)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8109 10 11) (extract v_8110 10 11)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8109 9 10) (extract v_8110 9 10)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8109 8 9) (extract v_8110 8 9)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (mux (eq v_8111 (expression.bv_nat 16 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (bv_xor (extract v_8109 0 1) (extract v_8110 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
