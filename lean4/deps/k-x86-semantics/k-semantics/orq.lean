def orq1 : instruction :=
  definst "orq" $ do
    pattern fun (v_3012 : imm int) (v_3013 : reg (bv 64)) => do
      v_4919 <- getRegister v_3013;
      v_4920 <- eval (handleImmediateWithSignExtend v_3012 32 32);
      v_4922 <- eval (bv_or v_4919 (leanSignExtend v_4920 64));
      setRegister (lhs.of_reg v_3013) v_4922;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_4919 63 64) (extract v_4920 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_4919 62 63) (extract v_4920 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4919 61 62) (extract v_4920 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4919 60 61) (extract v_4920 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4919 59 60) (extract v_4920 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4919 58 59) (extract v_4920 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4919 57 58) (extract v_4920 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4919 56 57) (extract v_4920 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4922);
      setRegister af undef;
      setRegister sf (extract v_4922 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3021 : reg (bv 64)) (v_3022 : reg (bv 64)) => do
      v_4982 <- getRegister v_3022;
      v_4983 <- getRegister v_3021;
      v_4984 <- eval (bv_or v_4982 v_4983);
      setRegister (lhs.of_reg v_3022) v_4984;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4984 56 64));
      setRegister zf (zeroFlag v_4984);
      setRegister af undef;
      setRegister sf (extract v_4984 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3017 : Mem) (v_3018 : reg (bv 64)) => do
      v_9235 <- getRegister v_3018;
      v_9236 <- evaluateAddress v_3017;
      v_9237 <- load v_9236 8;
      v_9238 <- eval (bv_or v_9235 v_9237);
      setRegister (lhs.of_reg v_3018) v_9238;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9238 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_9238);
      setRegister sf (extract v_9238 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3005 : imm int) (v_3004 : Mem) => do
      v_11189 <- evaluateAddress v_3004;
      v_11190 <- load v_11189 8;
      v_11191 <- eval (handleImmediateWithSignExtend v_3005 32 32);
      v_11193 <- eval (bv_or v_11190 (leanSignExtend v_11191 64));
      store v_11189 v_11193 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_11190 63 64) (extract v_11191 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_11190 62 63) (extract v_11191 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_11190 61 62) (extract v_11191 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_11190 60 61) (extract v_11191 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_11190 59 60) (extract v_11191 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_11190 58 59) (extract v_11191 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_11190 57 58) (extract v_11191 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_11190 56 57) (extract v_11191 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag v_11193);
      setRegister sf (extract v_11193 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3009 : reg (bv 64)) (v_3008 : Mem) => do
      v_11249 <- evaluateAddress v_3008;
      v_11250 <- load v_11249 8;
      v_11251 <- getRegister v_3009;
      v_11252 <- eval (bv_or v_11250 v_11251);
      store v_11249 v_11252 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11252 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_11252);
      setRegister sf (extract v_11252 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
