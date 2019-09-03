def rolw1 : instruction :=
  definst "rolw" $ do
    pattern fun cl (v_2656 : reg (bv 16)) => do
      v_5183 <- getRegister rcx;
      v_5185 <- eval (bv_and (extract v_5183 56 64) (expression.bv_nat 8 31));
      v_5186 <- eval (eq v_5185 (expression.bv_nat 8 0));
      v_5187 <- eval (notBool_ v_5186);
      v_5188 <- getRegister v_2656;
      v_5191 <- eval (rolHelper v_5188 (uvalueMInt (concat (expression.bv_nat 8 0) v_5185)) 0);
      v_5193 <- eval (eq (extract v_5191 15 16) (expression.bv_nat 1 1));
      v_5195 <- getRegister cf;
      v_5200 <- eval (eq v_5185 (expression.bv_nat 8 1));
      v_5208 <- getRegister of;
      setRegister (lhs.of_reg v_2656) v_5191;
      setRegister of (mux (bit_or (bit_and v_5200 (notBool_ (eq (eq (extract v_5191 0 1) (expression.bv_nat 1 1)) v_5193))) (bit_and (notBool_ v_5200) (bit_or (bit_and v_5187 undef) (bit_and v_5186 (eq v_5208 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5187 v_5193) (bit_and v_5186 (eq v_5195 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2659 : imm int) (v_2661 : reg (bv 16)) => do
      v_5219 <- eval (bv_and (handleImmediateWithSignExtend v_2659 8 8) (expression.bv_nat 8 31));
      v_5220 <- eval (eq v_5219 (expression.bv_nat 8 0));
      v_5221 <- eval (notBool_ v_5220);
      v_5222 <- getRegister v_2661;
      v_5225 <- eval (rolHelper v_5222 (uvalueMInt (concat (expression.bv_nat 8 0) v_5219)) 0);
      v_5227 <- eval (eq (extract v_5225 15 16) (expression.bv_nat 1 1));
      v_5229 <- getRegister cf;
      v_5234 <- eval (eq v_5219 (expression.bv_nat 8 1));
      v_5242 <- getRegister of;
      setRegister (lhs.of_reg v_2661) v_5225;
      setRegister of (mux (bit_or (bit_and v_5234 (notBool_ (eq (eq (extract v_5225 0 1) (expression.bv_nat 1 1)) v_5227))) (bit_and (notBool_ v_5234) (bit_or (bit_and v_5221 undef) (bit_and v_5220 (eq v_5242 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5221 v_5227) (bit_and v_5220 (eq v_5229 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2665 : reg (bv 16)) => do
      v_5252 <- getRegister v_2665;
      v_5257 <- eval (add (extract (shl v_5252 1) 0 16) (concat (expression.bv_nat 15 0) (extract v_5252 0 1)));
      v_5258 <- eval (extract v_5257 15 16);
      setRegister (lhs.of_reg v_2665) v_5257;
      setRegister of (mux (notBool_ (eq (eq (extract v_5257 0 1) (expression.bv_nat 1 1)) (eq v_5258 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5258;
      pure ()
    pat_end;
    pattern fun cl (v_2645 : Mem) => do
      v_14514 <- evaluateAddress v_2645;
      v_14515 <- load v_14514 2;
      v_14516 <- getRegister rcx;
      v_14518 <- eval (bv_and (extract v_14516 56 64) (expression.bv_nat 8 31));
      v_14521 <- eval (rolHelper v_14515 (uvalueMInt (concat (expression.bv_nat 8 0) v_14518)) 0);
      store v_14514 v_14521 2;
      v_14523 <- eval (eq v_14518 (expression.bv_nat 8 0));
      v_14524 <- eval (notBool_ v_14523);
      v_14526 <- eval (eq (extract v_14521 15 16) (expression.bv_nat 1 1));
      v_14528 <- getRegister cf;
      v_14533 <- eval (eq v_14518 (expression.bv_nat 8 1));
      v_14541 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14533 (notBool_ (eq (eq (extract v_14521 0 1) (expression.bv_nat 1 1)) v_14526))) (bit_and (notBool_ v_14533) (bit_or (bit_and v_14524 undef) (bit_and v_14523 (eq v_14541 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14524 v_14526) (bit_and v_14523 (eq v_14528 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2649 : imm int) (v_2648 : Mem) => do
      v_14550 <- evaluateAddress v_2648;
      v_14551 <- load v_14550 2;
      v_14553 <- eval (bv_and (handleImmediateWithSignExtend v_2649 8 8) (expression.bv_nat 8 31));
      v_14556 <- eval (rolHelper v_14551 (uvalueMInt (concat (expression.bv_nat 8 0) v_14553)) 0);
      store v_14550 v_14556 2;
      v_14558 <- eval (eq v_14553 (expression.bv_nat 8 0));
      v_14559 <- eval (notBool_ v_14558);
      v_14561 <- eval (eq (extract v_14556 15 16) (expression.bv_nat 1 1));
      v_14563 <- getRegister cf;
      v_14568 <- eval (eq v_14553 (expression.bv_nat 8 1));
      v_14576 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14568 (notBool_ (eq (eq (extract v_14556 0 1) (expression.bv_nat 1 1)) v_14561))) (bit_and (notBool_ v_14568) (bit_or (bit_and v_14559 undef) (bit_and v_14558 (eq v_14576 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14559 v_14561) (bit_and v_14558 (eq v_14563 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
