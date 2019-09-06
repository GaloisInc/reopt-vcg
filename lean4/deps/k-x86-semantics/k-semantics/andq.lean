def andq1 : instruction :=
  definst "andq" $ do
    pattern fun (v_2935 : imm int) (v_2936 : reg (bv 64)) => do
      v_5317 <- getRegister v_2936;
      v_5318 <- eval (handleImmediateWithSignExtend v_2935 32 32);
      v_5320 <- eval (bv_and v_5317 (sext v_5318 64));
      setRegister (lhs.of_reg v_2936) v_5320;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_5317 63 64) (extract v_5318 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_5317 62 63) (extract v_5318 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5317 61 62) (extract v_5318 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5317 60 61) (extract v_5318 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5317 59 60) (extract v_5318 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5317 58 59) (extract v_5318 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5317 57 58) (extract v_5318 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5317 56 57) (extract v_5318 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_5320 0);
      setRegister zf (zeroFlag v_5320);
      pure ()
    pat_end;
    pattern fun (v_2944 : reg (bv 64)) (v_2945 : reg (bv 64)) => do
      v_5379 <- getRegister v_2945;
      v_5380 <- getRegister v_2944;
      v_5381 <- eval (bv_and v_5379 v_5380);
      setRegister (lhs.of_reg v_2945) v_5381;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5381 56 64));
      setRegister sf (isBitSet v_5381 0);
      setRegister zf (zeroFlag v_5381);
      pure ()
    pat_end;
    pattern fun (v_2940 : Mem) (v_2941 : reg (bv 64)) => do
      v_9032 <- getRegister v_2941;
      v_9033 <- evaluateAddress v_2940;
      v_9034 <- load v_9033 8;
      v_9035 <- eval (bv_and v_9032 v_9034);
      setRegister (lhs.of_reg v_2941) v_9035;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_9035 56 64));
      setRegister sf (isBitSet v_9035 0);
      setRegister zf (zeroFlag v_9035);
      pure ()
    pat_end;
    pattern fun (v_2928 : imm int) (v_2927 : Mem) => do
      v_10359 <- evaluateAddress v_2927;
      v_10360 <- load v_10359 8;
      v_10361 <- eval (handleImmediateWithSignExtend v_2928 32 32);
      v_10363 <- eval (bv_and v_10360 (sext v_10361 64));
      store v_10359 v_10363 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_10360 63 64) (extract v_10361 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_10360 62 63) (extract v_10361 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10360 61 62) (extract v_10361 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10360 60 61) (extract v_10361 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10360 59 60) (extract v_10361 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10360 58 59) (extract v_10361 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10360 57 58) (extract v_10361 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_10360 56 57) (extract v_10361 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_10363 0);
      setRegister zf (zeroFlag v_10363);
      pure ()
    pat_end;
    pattern fun (v_2932 : reg (bv 64)) (v_2931 : Mem) => do
      v_10418 <- evaluateAddress v_2931;
      v_10419 <- load v_10418 8;
      v_10420 <- getRegister v_2932;
      v_10421 <- eval (bv_and v_10419 v_10420);
      store v_10418 v_10421 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10421 56 64));
      setRegister sf (isBitSet v_10421 0);
      setRegister zf (zeroFlag v_10421);
      pure ()
    pat_end
