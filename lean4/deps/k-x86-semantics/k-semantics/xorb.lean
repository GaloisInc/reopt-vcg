def xorb1 : instruction :=
  definst "xorb" $ do
    pattern fun (v_2711 : imm int) al => do
      v_4389 <- getRegister rax;
      v_4391 <- eval (handleImmediateWithSignExtend v_2711 8 8);
      v_4393 <- eval (bv_xor (extract v_4389 56 57) (extract v_4391 0 1));
      v_4395 <- eval (bv_xor (extract v_4389 56 64) v_4391);
      setRegister rax (concat (extract v_4389 0 56) v_4395);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_4389 63 64) (extract v_4391 7 8)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_4389 62 63) (extract v_4391 6 7)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4389 61 62) (extract v_4391 5 6)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4389 60 61) (extract v_4391 4 5)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4389 59 60) (extract v_4391 3 4)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4389 58 59) (extract v_4391 2 3)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4389 57 58) (extract v_4391 1 2)) (expression.bv_nat 1 1)))) (eq v_4393 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_4395 (expression.bv_nat 8 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister sf v_4393;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2727 : imm int) (v_2729 : reg (bv 8)) => do
      v_4464 <- getRegister v_2729;
      v_4466 <- eval (handleImmediateWithSignExtend v_2727 8 8);
      v_4468 <- eval (bv_xor (extract v_4464 0 1) (extract v_4466 0 1));
      v_4469 <- eval (bv_xor v_4464 v_4466);
      setRegister (lhs.of_reg v_2729) v_4469;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_4464 7 8) (extract v_4466 7 8)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_4464 6 7) (extract v_4466 6 7)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4464 5 6) (extract v_4466 5 6)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4464 4 5) (extract v_4466 4 5)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4464 3 4) (extract v_4466 3 4)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4464 2 3) (extract v_4466 2 3)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4464 1 2) (extract v_4466 1 2)) (expression.bv_nat 1 1)))) (eq v_4468 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_4469 (expression.bv_nat 8 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister sf v_4468;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2737 : reg (bv 8)) (v_2738 : reg (bv 8)) => do
      v_4528 <- getRegister v_2738;
      v_4530 <- getRegister v_2737;
      v_4532 <- eval (bv_xor (extract v_4528 0 1) (extract v_4530 0 1));
      v_4533 <- eval (bv_xor v_4528 v_4530);
      setRegister (lhs.of_reg v_2738) v_4533;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_4528 7 8) (extract v_4530 7 8)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_4528 6 7) (extract v_4530 6 7)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4528 5 6) (extract v_4530 5 6)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4528 4 5) (extract v_4530 4 5)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4528 3 4) (extract v_4530 3 4)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4528 2 3) (extract v_4530 2 3)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4528 1 2) (extract v_4530 1 2)) (expression.bv_nat 1 1)))) (eq v_4532 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_4533 (expression.bv_nat 8 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister sf v_4532;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2732 : Mem) (v_2733 : reg (bv 8)) => do
      v_7058 <- getRegister v_2733;
      v_7060 <- evaluateAddress v_2732;
      v_7061 <- load v_7060 1;
      v_7063 <- eval (bv_xor (extract v_7058 0 1) (extract v_7061 0 1));
      v_7064 <- eval (bv_xor v_7058 v_7061);
      setRegister (lhs.of_reg v_2733) v_7064;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_7058 7 8) (extract v_7061 7 8)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_7058 6 7) (extract v_7061 6 7)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7058 5 6) (extract v_7061 5 6)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7058 4 5) (extract v_7061 4 5)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7058 3 4) (extract v_7061 3 4)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7058 2 3) (extract v_7061 2 3)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7058 1 2) (extract v_7061 1 2)) (expression.bv_nat 1 1)))) (eq v_7063 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_7064 (expression.bv_nat 8 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister sf v_7063;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2715 : imm int) (v_2716 : Mem) => do
      v_7603 <- evaluateAddress v_2716;
      v_7604 <- load v_7603 1;
      v_7605 <- eval (handleImmediateWithSignExtend v_2715 8 8);
      v_7606 <- eval (bv_xor v_7604 v_7605);
      store v_7603 v_7606 1;
      v_7610 <- eval (bv_xor (extract v_7604 0 1) (extract v_7605 0 1));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_7604 7 8) (extract v_7605 7 8)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_7604 6 7) (extract v_7605 6 7)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7604 5 6) (extract v_7605 5 6)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7604 4 5) (extract v_7605 4 5)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7604 3 4) (extract v_7605 3 4)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7604 2 3) (extract v_7605 2 3)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7604 1 2) (extract v_7605 1 2)) (expression.bv_nat 1 1)))) (eq v_7610 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (mux (eq v_7606 (expression.bv_nat 8 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf v_7610;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2720 : reg (bv 8)) (v_2719 : Mem) => do
      v_7664 <- evaluateAddress v_2719;
      v_7665 <- load v_7664 1;
      v_7666 <- getRegister v_2720;
      v_7667 <- eval (bv_xor v_7665 v_7666);
      store v_7664 v_7667 1;
      v_7671 <- eval (bv_xor (extract v_7665 0 1) (extract v_7666 0 1));
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_7665 7 8) (extract v_7666 7 8)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_7665 6 7) (extract v_7666 6 7)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7665 5 6) (extract v_7666 5 6)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7665 4 5) (extract v_7666 4 5)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7665 3 4) (extract v_7666 3 4)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7665 2 3) (extract v_7666 2 3)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7665 1 2) (extract v_7666 1 2)) (expression.bv_nat 1 1)))) (eq v_7671 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (mux (eq v_7667 (expression.bv_nat 8 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf v_7671;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
