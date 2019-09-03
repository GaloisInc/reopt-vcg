def xaddw1 : instruction :=
  definst "xaddw" $ do
    pattern fun (v_2646 : reg (bv 16)) (v_2647 : reg (bv 16)) => do
      v_4193 <- eval (eq (eq (convToRegKeysHelper (convSubRegsToRegs v_2646)) (convToRegKeysHelper (convSubRegsToRegs v_2647))) bit_zero);
      v_4194 <- getRegister v_2646;
      v_4196 <- getRegister v_2647;
      v_4198 <- eval (add (concat (expression.bv_nat 1 0) v_4194) (concat (expression.bv_nat 1 0) v_4196));
      v_4200 <- eval (extract v_4198 1 2);
      v_4201 <- eval (extract v_4198 1 17);
      v_4207 <- eval (extract v_4198 12 13);
      v_4241 <- eval (eq (extract v_4194 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2647) v_4201;
      setRegister (lhs.of_reg v_2646) v_4196;
      setRegister of (mux (bit_and (eq v_4241 (eq (extract v_4196 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4241 (eq v_4200 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4198 16 17) (expression.bv_nat 1 1)) (eq (extract v_4198 15 16) (expression.bv_nat 1 1)))) (eq (extract v_4198 14 15) (expression.bv_nat 1 1)))) (eq (extract v_4198 13 14) (expression.bv_nat 1 1)))) (eq v_4207 (expression.bv_nat 1 1)))) (eq (extract v_4198 11 12) (expression.bv_nat 1 1)))) (eq (extract v_4198 10 11) (expression.bv_nat 1 1)))) (eq (extract v_4198 9 10) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (bv_xor (bv_xor (extract v_4194 11 12) (extract v_4196 11 12)) v_4207);
      setRegister zf (mux (eq v_4201 (expression.bv_nat 16 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf v_4200;
      setRegister cf (extract v_4198 0 1);
      pure ()
    pat_end;
    pattern fun (v_2651 : reg (bv 16)) (v_2652 : reg (bv 16)) => do
      v_4262 <- eval (eq (convToRegKeysHelper (convSubRegsToRegs v_2651)) (convToRegKeysHelper (convSubRegsToRegs v_2652)));
      v_4263 <- getRegister v_2652;
      v_4265 <- eval (add (concat (expression.bv_nat 1 0) v_4263) (concat (expression.bv_nat 1 0) v_4263));
      v_4267 <- eval (extract v_4265 1 2);
      v_4268 <- eval (extract v_4265 1 17);
      v_4271 <- eval (extract v_4265 12 13);
      setRegister (lhs.of_reg v_2652) v_4268;
      setRegister of (mux (notBool_ (eq (eq (extract v_4263 0 1) (expression.bv_nat 1 1)) (eq v_4267 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4265 16 17) (expression.bv_nat 1 1)) (eq (extract v_4265 15 16) (expression.bv_nat 1 1)))) (eq (extract v_4265 14 15) (expression.bv_nat 1 1)))) (eq (extract v_4265 13 14) (expression.bv_nat 1 1)))) (eq v_4271 (expression.bv_nat 1 1)))) (eq (extract v_4265 11 12) (expression.bv_nat 1 1)))) (eq (extract v_4265 10 11) (expression.bv_nat 1 1)))) (eq (extract v_4265 9 10) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af v_4271;
      setRegister zf (mux (eq v_4268 (expression.bv_nat 16 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf v_4267;
      setRegister cf (extract v_4265 0 1);
      pure ()
    pat_end;
    pattern fun (v_2643 : reg (bv 16)) (v_2642 : Mem) => do
      v_7518 <- evaluateAddress v_2642;
      v_7519 <- getRegister v_2643;
      v_7521 <- load v_7518 2;
      v_7523 <- eval (add (concat (expression.bv_nat 1 0) v_7519) (concat (expression.bv_nat 1 0) v_7521));
      v_7524 <- eval (extract v_7523 1 17);
      store v_7518 v_7524 2;
      v_7527 <- eval (extract v_7523 1 2);
      v_7531 <- eval (extract v_7523 12 13);
      v_7567 <- eval (eq (extract v_7519 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2643) v_7521;
      setRegister of (mux (bit_and (eq v_7567 (eq (extract v_7521 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7567 (eq v_7527 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7523 16 17) (expression.bv_nat 1 1)) (eq (extract v_7523 15 16) (expression.bv_nat 1 1)))) (eq (extract v_7523 14 15) (expression.bv_nat 1 1)))) (eq (extract v_7523 13 14) (expression.bv_nat 1 1)))) (eq v_7531 (expression.bv_nat 1 1)))) (eq (extract v_7523 11 12) (expression.bv_nat 1 1)))) (eq (extract v_7523 10 11) (expression.bv_nat 1 1)))) (eq (extract v_7523 9 10) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_7524 (expression.bv_nat 16 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (bv_xor (bv_xor (extract v_7519 11 12) (extract v_7521 11 12)) v_7531);
      setRegister sf v_7527;
      setRegister cf (extract v_7523 0 1);
      pure ()
    pat_end
