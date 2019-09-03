def adcq1 : instruction :=
  definst "adcq" $ do
    pattern fun (v_2468 : imm int) (v_2470 : reg (bv 64)) => do
      v_4153 <- getRegister cf;
      v_4155 <- eval (handleImmediateWithSignExtend v_2468 32 32);
      v_4157 <- eval (mi 64 (svalueMInt v_4155));
      v_4158 <- eval (concat (expression.bv_nat 1 0) v_4157);
      v_4161 <- getRegister v_2470;
      v_4163 <- eval (add (mux (eq v_4153 (expression.bv_nat 1 1)) (add v_4158 (expression.bv_nat 65 1)) v_4158) (concat (expression.bv_nat 1 0) v_4161));
      v_4165 <- eval (extract v_4163 1 2);
      v_4171 <- eval (extract v_4163 1 65);
      v_4176 <- eval (eq (extract v_4157 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2470) v_4171;
      setRegister of (mux (bit_and (eq v_4176 (eq (extract v_4161 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4176 (eq v_4165 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4163 57 65));
      setRegister zf (zeroFlag v_4171);
      setRegister af (bv_xor (bv_xor (extract v_4155 27 28) (extract v_4161 59 60)) (extract v_4163 60 61));
      setRegister sf v_4165;
      setRegister cf (extract v_4163 0 1);
      pure ()
    pat_end;
    pattern fun (v_2478 : reg (bv 64)) (v_2479 : reg (bv 64)) => do
      v_4196 <- getRegister cf;
      v_4198 <- getRegister v_2478;
      v_4199 <- eval (concat (expression.bv_nat 1 0) v_4198);
      v_4202 <- getRegister v_2479;
      v_4204 <- eval (add (mux (eq v_4196 (expression.bv_nat 1 1)) (add v_4199 (expression.bv_nat 65 1)) v_4199) (concat (expression.bv_nat 1 0) v_4202));
      v_4206 <- eval (extract v_4204 1 2);
      v_4211 <- eval (extract v_4204 1 65);
      v_4216 <- eval (eq (extract v_4198 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2479) v_4211;
      setRegister of (mux (bit_and (eq v_4216 (eq (extract v_4202 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4216 (eq v_4206 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4204 57 65));
      setRegister zf (zeroFlag v_4211);
      setRegister af (bv_xor (extract (bv_xor v_4198 v_4202) 59 60) (extract v_4204 60 61));
      setRegister sf v_4206;
      setRegister cf (extract v_4204 0 1);
      pure ()
    pat_end;
    pattern fun (v_2473 : Mem) (v_2474 : reg (bv 64)) => do
      v_8923 <- getRegister cf;
      v_8925 <- evaluateAddress v_2473;
      v_8926 <- load v_8925 8;
      v_8927 <- eval (concat (expression.bv_nat 1 0) v_8926);
      v_8930 <- getRegister v_2474;
      v_8932 <- eval (add (mux (eq v_8923 (expression.bv_nat 1 1)) (add v_8927 (expression.bv_nat 65 1)) v_8927) (concat (expression.bv_nat 1 0) v_8930));
      v_8934 <- eval (extract v_8932 1 2);
      v_8935 <- eval (extract v_8932 1 65);
      v_8944 <- eval (eq (extract v_8926 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2474) v_8935;
      setRegister of (mux (bit_and (eq v_8944 (eq (extract v_8930 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8944 (eq v_8934 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8932 57 65));
      setRegister af (bv_xor (extract (bv_xor v_8926 v_8930) 59 60) (extract v_8932 60 61));
      setRegister zf (zeroFlag v_8935);
      setRegister sf v_8934;
      setRegister cf (extract v_8932 0 1);
      pure ()
    pat_end;
    pattern fun (v_2461 : imm int) (v_2460 : Mem) => do
      v_10421 <- evaluateAddress v_2460;
      v_10422 <- getRegister cf;
      v_10424 <- eval (handleImmediateWithSignExtend v_2461 32 32);
      v_10426 <- eval (mi 64 (svalueMInt v_10424));
      v_10427 <- eval (concat (expression.bv_nat 1 0) v_10426);
      v_10430 <- load v_10421 8;
      v_10432 <- eval (add (mux (eq v_10422 (expression.bv_nat 1 1)) (add v_10427 (expression.bv_nat 65 1)) v_10427) (concat (expression.bv_nat 1 0) v_10430));
      v_10433 <- eval (extract v_10432 1 65);
      store v_10421 v_10433 8;
      v_10436 <- eval (extract v_10432 1 2);
      v_10446 <- eval (eq (extract v_10426 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10446 (eq (extract v_10430 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10446 (eq v_10436 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10432 57 65));
      setRegister af (bv_xor (bv_xor (extract v_10424 27 28) (extract v_10430 59 60)) (extract v_10432 60 61));
      setRegister zf (zeroFlag v_10433);
      setRegister sf v_10436;
      setRegister cf (extract v_10432 0 1);
      pure ()
    pat_end;
    pattern fun (v_2465 : reg (bv 64)) (v_2464 : Mem) => do
      v_10461 <- evaluateAddress v_2464;
      v_10462 <- getRegister cf;
      v_10464 <- getRegister v_2465;
      v_10465 <- eval (concat (expression.bv_nat 1 0) v_10464);
      v_10468 <- load v_10461 8;
      v_10470 <- eval (add (mux (eq v_10462 (expression.bv_nat 1 1)) (add v_10465 (expression.bv_nat 65 1)) v_10465) (concat (expression.bv_nat 1 0) v_10468));
      v_10471 <- eval (extract v_10470 1 65);
      store v_10461 v_10471 8;
      v_10474 <- eval (extract v_10470 1 2);
      v_10483 <- eval (eq (extract v_10464 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10483 (eq (extract v_10468 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10483 (eq v_10474 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10470 57 65));
      setRegister af (bv_xor (extract (bv_xor v_10464 v_10468) 59 60) (extract v_10470 60 61));
      setRegister zf (zeroFlag v_10471);
      setRegister sf v_10474;
      setRegister cf (extract v_10470 0 1);
      pure ()
    pat_end
