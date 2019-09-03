def adcq1 : instruction :=
  definst "adcq" $ do
    pattern fun (v_2483 : imm int) (v_2482 : reg (bv 64)) => do
      v_4166 <- getRegister cf;
      v_4168 <- eval (handleImmediateWithSignExtend v_2483 32 32);
      v_4169 <- eval (leanSignExtend v_4168 64);
      v_4170 <- eval (concat (expression.bv_nat 1 0) v_4169);
      v_4173 <- getRegister v_2482;
      v_4175 <- eval (add (mux (eq v_4166 (expression.bv_nat 1 1)) (add v_4170 (expression.bv_nat 65 1)) v_4170) (concat (expression.bv_nat 1 0) v_4173));
      v_4177 <- eval (extract v_4175 1 2);
      v_4183 <- eval (extract v_4175 1 65);
      v_4188 <- eval (eq (extract v_4169 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2482) v_4183;
      setRegister of (mux (bit_and (eq v_4188 (eq (extract v_4173 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4188 (eq v_4177 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4175 57 65));
      setRegister zf (zeroFlag v_4183);
      setRegister af (bv_xor (bv_xor (extract v_4168 27 28) (extract v_4173 59 60)) (extract v_4175 60 61));
      setRegister sf v_4177;
      setRegister cf (extract v_4175 0 1);
      pure ()
    pat_end;
    pattern fun (v_2491 : reg (bv 64)) (v_2492 : reg (bv 64)) => do
      v_4208 <- getRegister cf;
      v_4210 <- getRegister v_2491;
      v_4211 <- eval (concat (expression.bv_nat 1 0) v_4210);
      v_4214 <- getRegister v_2492;
      v_4216 <- eval (add (mux (eq v_4208 (expression.bv_nat 1 1)) (add v_4211 (expression.bv_nat 65 1)) v_4211) (concat (expression.bv_nat 1 0) v_4214));
      v_4218 <- eval (extract v_4216 1 2);
      v_4223 <- eval (extract v_4216 1 65);
      v_4228 <- eval (eq (extract v_4210 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2492) v_4223;
      setRegister of (mux (bit_and (eq v_4228 (eq (extract v_4214 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4228 (eq v_4218 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4216 57 65));
      setRegister zf (zeroFlag v_4223);
      setRegister af (bv_xor (extract (bv_xor v_4210 v_4214) 59 60) (extract v_4216 60 61));
      setRegister sf v_4218;
      setRegister cf (extract v_4216 0 1);
      pure ()
    pat_end;
    pattern fun (v_2486 : Mem) (v_2487 : reg (bv 64)) => do
      v_9063 <- getRegister cf;
      v_9065 <- evaluateAddress v_2486;
      v_9066 <- load v_9065 8;
      v_9067 <- eval (concat (expression.bv_nat 1 0) v_9066);
      v_9070 <- getRegister v_2487;
      v_9072 <- eval (add (mux (eq v_9063 (expression.bv_nat 1 1)) (add v_9067 (expression.bv_nat 65 1)) v_9067) (concat (expression.bv_nat 1 0) v_9070));
      v_9074 <- eval (extract v_9072 1 2);
      v_9079 <- eval (extract v_9072 1 65);
      v_9084 <- eval (eq (extract v_9066 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2487) v_9079;
      setRegister of (mux (bit_and (eq v_9084 (eq (extract v_9070 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_9084 (eq v_9074 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9072 57 65));
      setRegister zf (zeroFlag v_9079);
      setRegister af (bv_xor (extract (bv_xor v_9066 v_9070) 59 60) (extract v_9072 60 61));
      setRegister sf v_9074;
      setRegister cf (extract v_9072 0 1);
      pure ()
    pat_end;
    pattern fun (v_2474 : imm int) (v_2473 : Mem) => do
      v_10707 <- evaluateAddress v_2473;
      v_10708 <- getRegister cf;
      v_10710 <- eval (handleImmediateWithSignExtend v_2474 32 32);
      v_10711 <- eval (leanSignExtend v_10710 64);
      v_10712 <- eval (concat (expression.bv_nat 1 0) v_10711);
      v_10715 <- load v_10707 8;
      v_10717 <- eval (add (mux (eq v_10708 (expression.bv_nat 1 1)) (add v_10712 (expression.bv_nat 65 1)) v_10712) (concat (expression.bv_nat 1 0) v_10715));
      v_10718 <- eval (extract v_10717 1 65);
      store v_10707 v_10718 8;
      v_10721 <- eval (extract v_10717 1 2);
      v_10731 <- eval (eq (extract v_10711 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10731 (eq (extract v_10715 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10731 (eq v_10721 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10717 57 65));
      setRegister af (bv_xor (bv_xor (extract v_10710 27 28) (extract v_10715 59 60)) (extract v_10717 60 61));
      setRegister zf (zeroFlag v_10718);
      setRegister sf v_10721;
      setRegister cf (extract v_10717 0 1);
      pure ()
    pat_end;
    pattern fun (v_2478 : reg (bv 64)) (v_2477 : Mem) => do
      v_10746 <- evaluateAddress v_2477;
      v_10747 <- getRegister cf;
      v_10749 <- getRegister v_2478;
      v_10750 <- eval (concat (expression.bv_nat 1 0) v_10749);
      v_10753 <- load v_10746 8;
      v_10755 <- eval (add (mux (eq v_10747 (expression.bv_nat 1 1)) (add v_10750 (expression.bv_nat 65 1)) v_10750) (concat (expression.bv_nat 1 0) v_10753));
      v_10756 <- eval (extract v_10755 1 65);
      store v_10746 v_10756 8;
      v_10759 <- eval (extract v_10755 1 2);
      v_10768 <- eval (eq (extract v_10749 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10768 (eq (extract v_10753 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10768 (eq v_10759 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10755 57 65));
      setRegister af (bv_xor (extract (bv_xor v_10749 v_10753) 59 60) (extract v_10755 60 61));
      setRegister zf (zeroFlag v_10756);
      setRegister sf v_10759;
      setRegister cf (extract v_10755 0 1);
      pure ()
    pat_end
