def andl1 : instruction :=
  definst "andl" $ do
    pattern fun (v_2766 : imm int) eax => do
      v_5451 <- getRegister rax;
      v_5453 <- eval (handleImmediateWithSignExtend v_2766 32 32);
      v_5457 <- eval (bv_and (extract v_5451 32 64) v_5453);
      setRegister eax v_5457;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_5451 63 64) (extract v_5453 31 32)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_5451 62 63) (extract v_5453 30 31)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5451 61 62) (extract v_5453 29 30)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5451 60 61) (extract v_5453 28 29)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5451 59 60) (extract v_5453 27 28)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5451 58 59) (extract v_5453 26 27)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5451 57 58) (extract v_5453 25 26)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5451 56 57) (extract v_5453 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5457);
      setRegister af undef;
      setRegister sf (bv_and (extract v_5451 32 33) (extract v_5453 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2779 : imm int) (v_2778 : reg (bv 32)) => do
      v_5520 <- getRegister v_2778;
      v_5522 <- eval (bv_and v_5520 (handleImmediateWithSignExtend v_2779 32 32));
      setRegister (lhs.of_reg v_2778) v_5522;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5522 24 32));
      setRegister zf (zeroFlag v_5522);
      setRegister af undef;
      setRegister sf (extract v_5522 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2787 : reg (bv 32)) (v_2788 : reg (bv 32)) => do
      v_5538 <- getRegister v_2788;
      v_5539 <- getRegister v_2787;
      v_5540 <- eval (bv_and v_5538 v_5539);
      setRegister (lhs.of_reg v_2788) v_5540;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5540 24 32));
      setRegister zf (zeroFlag v_5540);
      setRegister af undef;
      setRegister sf (extract v_5540 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2782 : Mem) (v_2783 : reg (bv 32)) => do
      v_9632 <- getRegister v_2783;
      v_9633 <- evaluateAddress v_2782;
      v_9634 <- load v_9633 4;
      v_9635 <- eval (bv_and v_9632 v_9634);
      setRegister (lhs.of_reg v_2783) v_9635;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9635 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_9635);
      setRegister sf (extract v_9635 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2770 : imm int) (v_2769 : Mem) => do
      v_11198 <- evaluateAddress v_2769;
      v_11199 <- load v_11198 4;
      v_11201 <- eval (bv_and v_11199 (handleImmediateWithSignExtend v_2770 32 32));
      store v_11198 v_11201 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11201 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_11201);
      setRegister sf (extract v_11201 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2774 : reg (bv 32)) (v_2773 : Mem) => do
      v_11213 <- evaluateAddress v_2773;
      v_11214 <- load v_11213 4;
      v_11215 <- getRegister v_2774;
      v_11216 <- eval (bv_and v_11214 v_11215);
      store v_11213 v_11216 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11216 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_11216);
      setRegister sf (extract v_11216 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
