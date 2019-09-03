def andb1 : instruction :=
  definst "andb" $ do
    pattern fun (v_2711 : imm int) al => do
      v_5287 <- getRegister rax;
      v_5289 <- eval (handleImmediateWithSignExtend v_2711 8 8);
      v_5291 <- eval (bv_and (extract v_5287 56 57) (extract v_5289 0 1));
      v_5293 <- eval (bv_and (extract v_5287 56 64) v_5289);
      setRegister rax (concat (extract v_5287 0 56) v_5293);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_5287 63 64) (extract v_5289 7 8)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_5287 62 63) (extract v_5289 6 7)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5287 61 62) (extract v_5289 5 6)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5287 60 61) (extract v_5289 4 5)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5287 59 60) (extract v_5289 3 4)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5287 58 59) (extract v_5289 2 3)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5287 57 58) (extract v_5289 1 2)) (expression.bv_nat 1 1)))) (eq v_5291 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5293);
      setRegister af undef;
      setRegister sf v_5291;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2727 : imm int) (v_2729 : reg (bv 8)) => do
      v_5359 <- getRegister v_2729;
      v_5361 <- eval (bv_and v_5359 (handleImmediateWithSignExtend v_2727 8 8));
      setRegister (lhs.of_reg v_2729) v_5361;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5361 0 8));
      setRegister zf (zeroFlag v_5361);
      setRegister af undef;
      setRegister sf (extract v_5361 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2737 : reg (bv 8)) (v_2738 : reg (bv 8)) => do
      v_5377 <- getRegister v_2738;
      v_5378 <- getRegister v_2737;
      v_5379 <- eval (bv_and v_5377 v_5378);
      setRegister (lhs.of_reg v_2738) v_5379;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5379 0 8));
      setRegister zf (zeroFlag v_5379);
      setRegister af undef;
      setRegister sf (extract v_5379 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2746 : imm int) (v_2748 : reg (bv 8)) => do
      v_5405 <- getRegister v_2748;
      v_5407 <- eval (bv_and v_5405 (handleImmediateWithSignExtend v_2746 8 8));
      setRegister (lhs.of_reg v_2748) v_5407;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5407 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_5407);
      setRegister sf (extract v_5407 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2757 : reg (bv 8)) (v_2756 : reg (bv 8)) => do
      v_5423 <- getRegister v_2756;
      v_5424 <- getRegister v_2757;
      v_5425 <- eval (bv_and v_5423 v_5424);
      setRegister (lhs.of_reg v_2756) v_5425;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5425 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_5425);
      setRegister sf (extract v_5425 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2732 : Mem) (v_2733 : reg (bv 8)) => do
      v_9600 <- getRegister v_2733;
      v_9601 <- evaluateAddress v_2732;
      v_9602 <- load v_9601 1;
      v_9603 <- eval (bv_and v_9600 v_9602);
      setRegister (lhs.of_reg v_2733) v_9603;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9603 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_9603);
      setRegister sf (extract v_9603 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2751 : Mem) (v_2752 : reg (bv 8)) => do
      v_9615 <- getRegister v_2752;
      v_9616 <- evaluateAddress v_2751;
      v_9617 <- load v_9616 1;
      v_9618 <- eval (bv_and v_9615 v_9617);
      setRegister (lhs.of_reg v_2752) v_9618;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9618 0 8));
      setRegister zf (zeroFlag v_9618);
      setRegister af undef;
      setRegister sf (extract v_9618 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2716 : imm int) (v_2715 : Mem) => do
      v_11153 <- evaluateAddress v_2715;
      v_11154 <- load v_11153 1;
      v_11156 <- eval (bv_and v_11154 (handleImmediateWithSignExtend v_2716 8 8));
      store v_11153 v_11156 1;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11156 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_11156);
      setRegister sf (extract v_11156 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2720 : reg (bv 8)) (v_2719 : Mem) => do
      v_11168 <- evaluateAddress v_2719;
      v_11169 <- load v_11168 1;
      v_11170 <- getRegister v_2720;
      v_11171 <- eval (bv_and v_11169 v_11170);
      store v_11168 v_11171 1;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11171 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_11171);
      setRegister sf (extract v_11171 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
