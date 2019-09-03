def andl1 : instruction :=
  definst "andl" $ do
    pattern fun (v_2752 : imm int) eax => do
      v_5274 <- getRegister rax;
      v_5276 <- eval (handleImmediateWithSignExtend v_2752 32 32);
      v_5280 <- eval (bv_and (extract v_5274 32 64) v_5276);
      setRegister eax v_5280;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_5274 63 64) (extract v_5276 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_5274 62 63) (extract v_5276 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5274 61 62) (extract v_5276 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5274 60 61) (extract v_5276 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5274 59 60) (extract v_5276 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5274 58 59) (extract v_5276 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5274 57 58) (extract v_5276 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5274 56 57) (extract v_5276 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5280);
      setRegister af undef;
      setRegister sf (bv_and (extract v_5274 32 33) (extract v_5276 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2764 : imm int) (v_2766 : reg (bv 32)) => do
      v_5343 <- getRegister v_2766;
      v_5345 <- eval (bv_and v_5343 (handleImmediateWithSignExtend v_2764 32 32));
      setRegister (lhs.of_reg v_2766) v_5345;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5345 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_5345);
      setRegister sf (extract v_5345 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2774 : reg (bv 32)) (v_2775 : reg (bv 32)) => do
      v_5361 <- getRegister v_2775;
      v_5362 <- getRegister v_2774;
      v_5363 <- eval (bv_and v_5361 v_5362);
      setRegister (lhs.of_reg v_2775) v_5363;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5363 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_5363);
      setRegister sf (extract v_5363 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2769 : Mem) (v_2770 : reg (bv 32)) => do
      v_9324 <- getRegister v_2770;
      v_9325 <- evaluateAddress v_2769;
      v_9326 <- load v_9325 4;
      v_9327 <- eval (bv_and v_9324 v_9326);
      setRegister (lhs.of_reg v_2770) v_9327;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9327 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_9327);
      setRegister sf (extract v_9327 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2757 : imm int) (v_2756 : Mem) => do
      v_10914 <- evaluateAddress v_2756;
      v_10915 <- load v_10914 4;
      v_10917 <- eval (bv_and v_10915 (handleImmediateWithSignExtend v_2757 32 32));
      store v_10914 v_10917 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_10917 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_10917);
      setRegister sf (extract v_10917 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2761 : reg (bv 32)) (v_2760 : Mem) => do
      v_10929 <- evaluateAddress v_2760;
      v_10930 <- load v_10929 4;
      v_10931 <- getRegister v_2761;
      v_10932 <- eval (bv_and v_10930 v_10931);
      store v_10929 v_10932 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_10932 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_10932);
      setRegister sf (extract v_10932 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
