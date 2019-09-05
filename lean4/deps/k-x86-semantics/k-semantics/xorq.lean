def xorq1 : instruction :=
  definst "xorq" $ do
    pattern fun (v_3440 : imm int) (v_3439 : reg (bv 64)) => do
      v_8047 <- getRegister v_3439;
      v_8048 <- eval (handleImmediateWithSignExtend v_3440 32 32);
      v_8050 <- eval (bv_xor v_8047 (sext v_8048 64));
      setRegister (lhs.of_reg v_3439) v_8050;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_8047 63 64) (extract v_8048 31 32)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_8047 62 63) (extract v_8048 30 31)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8047 61 62) (extract v_8048 29 30)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8047 60 61) (extract v_8048 28 29)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8047 59 60) (extract v_8048 27 28)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8047 58 59) (extract v_8048 26 27)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8047 57 58) (extract v_8048 25 26)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_8047 56 57) (extract v_8048 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_8050 0);
      setRegister zf (zeroFlag v_8050);
      pure ()
    pat_end;
    pattern fun (v_3448 : reg (bv 64)) (v_3449 : reg (bv 64)) => do
      v_8109 <- getRegister v_3449;
      v_8110 <- getRegister v_3448;
      v_8111 <- eval (bv_xor v_8109 v_8110);
      setRegister (lhs.of_reg v_3449) v_8111;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8111 56 64));
      setRegister sf (isBitSet v_8111 0);
      setRegister zf (zeroFlag v_8111);
      pure ()
    pat_end;
    pattern fun (v_3443 : Mem) (v_3444 : reg (bv 64)) => do
      v_13574 <- getRegister v_3444;
      v_13575 <- evaluateAddress v_3443;
      v_13576 <- load v_13575 8;
      v_13577 <- eval (bv_xor v_13574 v_13576);
      setRegister (lhs.of_reg v_3444) v_13577;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13577 56 64));
      setRegister sf (isBitSet v_13577 0);
      setRegister zf (zeroFlag v_13577);
      pure ()
    pat_end;
    pattern fun (v_3431 : imm int) (v_3430 : Mem) => do
      v_13681 <- evaluateAddress v_3430;
      v_13682 <- load v_13681 8;
      v_13683 <- eval (handleImmediateWithSignExtend v_3431 32 32);
      v_13685 <- eval (bv_xor v_13682 (sext v_13683 64));
      store v_13681 v_13685 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_13682 63 64) (extract v_13683 31 32)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_13682 62 63) (extract v_13683 30 31)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_13682 61 62) (extract v_13683 29 30)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_13682 60 61) (extract v_13683 28 29)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_13682 59 60) (extract v_13683 27 28)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_13682 58 59) (extract v_13683 26 27)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_13682 57 58) (extract v_13683 25 26)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_13682 56 57) (extract v_13683 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_13685 0);
      setRegister zf (zeroFlag v_13685);
      pure ()
    pat_end;
    pattern fun (v_3435 : reg (bv 64)) (v_3434 : Mem) => do
      v_13740 <- evaluateAddress v_3434;
      v_13741 <- load v_13740 8;
      v_13742 <- getRegister v_3435;
      v_13743 <- eval (bv_xor v_13741 v_13742);
      store v_13740 v_13743 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13743 56 64));
      setRegister sf (isBitSet v_13743 0);
      setRegister zf (zeroFlag v_13743);
      pure ()
    pat_end
