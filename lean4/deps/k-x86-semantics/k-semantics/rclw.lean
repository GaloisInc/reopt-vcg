def rclw1 : instruction :=
  definst "rclw" $ do
    pattern fun cl (v_2425 : reg (bv 16)) => do
      v_4105 <- getRegister cf;
      v_4108 <- getRegister v_2425;
      v_4110 <- getRegister rcx;
      v_4114 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_4110 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4116 <- eval (rolHelper (concat (mux (eq v_4105 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4108) (uvalueMInt v_4114) 0);
      v_4117 <- eval (extract v_4116 0 1);
      v_4118 <- eval (extract v_4114 9 17);
      v_4119 <- eval (eq v_4118 (expression.bv_nat 8 1));
      v_4127 <- eval (eq v_4118 (expression.bv_nat 8 0));
      v_4130 <- getRegister of;
      setRegister (lhs.of_reg v_2425) (extract v_4116 1 17);
      setRegister of (mux (bit_or (bit_and v_4119 (notBool_ (eq (eq v_4117 (expression.bv_nat 1 1)) (eq (extract v_4116 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4119) (bit_or (bit_and (notBool_ v_4127) undef) (bit_and v_4127 (eq v_4130 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4117;
      pure ()
    pat_end;
    pattern fun (v_2428 : imm int) (v_2430 : reg (bv 16)) => do
      v_4141 <- getRegister cf;
      v_4144 <- getRegister v_2430;
      v_4149 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2428 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4151 <- eval (rolHelper (concat (mux (eq v_4141 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4144) (uvalueMInt v_4149) 0);
      v_4152 <- eval (extract v_4151 0 1);
      v_4153 <- eval (extract v_4149 9 17);
      v_4154 <- eval (eq v_4153 (expression.bv_nat 8 1));
      v_4162 <- eval (eq v_4153 (expression.bv_nat 8 0));
      v_4165 <- getRegister of;
      setRegister (lhs.of_reg v_2430) (extract v_4151 1 17);
      setRegister of (mux (bit_or (bit_and v_4154 (notBool_ (eq (eq v_4152 (expression.bv_nat 1 1)) (eq (extract v_4151 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4154) (bit_or (bit_and (notBool_ v_4162) undef) (bit_and v_4162 (eq v_4165 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4152;
      pure ()
    pat_end;
    pattern fun $0x1 (v_2434 : reg (bv 16)) => do
      v_4176 <- getRegister cf;
      v_4178 <- eval (mux (eq v_4176 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_4179 <- getRegister v_2434;
      v_4180 <- eval (concat v_4178 v_4179);
      v_4183 <- eval (add (bitwidthMInt v_4178) 16);
      v_4189 <- eval (add (extract (shl v_4180 1) 0 v_4183) (concat (mi (sub v_4183 1) 0) (extract v_4180 0 1)));
      v_4190 <- eval (extract v_4189 0 1);
      setRegister (lhs.of_reg v_2434) (extract v_4189 1 17);
      setRegister of (mux (notBool_ (eq (eq v_4190 (expression.bv_nat 1 1)) (eq (extract v_4189 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4190;
      pure ()
    pat_end;
    pattern fun cl (v_2414 : Mem) => do
      v_13458 <- evaluateAddress v_2414;
      v_13459 <- getRegister cf;
      v_13462 <- load v_13458 2;
      v_13464 <- getRegister rcx;
      v_13468 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_13464 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_13470 <- eval (rolHelper (concat (mux (eq v_13459 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13462) (uvalueMInt v_13468) 0);
      store v_13458 (extract v_13470 1 17) 2;
      v_13473 <- eval (extract v_13470 0 1);
      v_13474 <- eval (extract v_13468 9 17);
      v_13475 <- eval (eq v_13474 (expression.bv_nat 8 1));
      v_13483 <- eval (eq v_13474 (expression.bv_nat 8 0));
      v_13486 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13475 (notBool_ (eq (eq v_13473 (expression.bv_nat 1 1)) (eq (extract v_13470 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13475) (bit_or (bit_and (notBool_ v_13483) undef) (bit_and v_13483 (eq v_13486 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_13473;
      pure ()
    pat_end;
    pattern fun (v_2418 : imm int) (v_2417 : Mem) => do
      v_13495 <- evaluateAddress v_2417;
      v_13496 <- getRegister cf;
      v_13499 <- load v_13495 2;
      v_13504 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2418 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_13506 <- eval (rolHelper (concat (mux (eq v_13496 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13499) (uvalueMInt v_13504) 0);
      store v_13495 (extract v_13506 1 17) 2;
      v_13509 <- eval (extract v_13506 0 1);
      v_13510 <- eval (extract v_13504 9 17);
      v_13511 <- eval (eq v_13510 (expression.bv_nat 8 1));
      v_13519 <- eval (eq v_13510 (expression.bv_nat 8 0));
      v_13522 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13511 (notBool_ (eq (eq v_13509 (expression.bv_nat 1 1)) (eq (extract v_13506 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13511) (bit_or (bit_and (notBool_ v_13519) undef) (bit_and v_13519 (eq v_13522 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_13509;
      pure ()
    pat_end
