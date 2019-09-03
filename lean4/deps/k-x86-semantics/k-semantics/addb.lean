def addb1 : instruction :=
  definst "addb" $ do
    pattern fun (v_2525 : imm int) al => do
      v_4406 <- eval (handleImmediateWithSignExtend v_2525 8 8);
      v_4408 <- getRegister rax;
      v_4411 <- eval (add (concat (expression.bv_nat 1 0) v_4406) (concat (expression.bv_nat 1 0) (extract v_4408 56 64)));
      v_4413 <- eval (extract v_4411 1 2);
      v_4419 <- eval (extract v_4411 1 9);
      v_4423 <- eval (eq (extract v_4406 0 1) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_4408 0 56) v_4419);
      setRegister of (mux (bit_and (eq v_4423 (eq (extract v_4408 56 57) (expression.bv_nat 1 1))) (notBool_ (eq v_4423 (eq v_4413 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_4419);
      setRegister zf (zeroFlag v_4419);
      setRegister af (bv_xor (bv_xor (extract v_4406 3 4) (extract v_4408 59 60)) (extract v_4411 4 5));
      setRegister sf v_4413;
      setRegister cf (extract v_4411 0 1);
      pure ()
    pat_end;
    pattern fun (v_2541 : imm int) (v_2543 : reg (bv 8)) => do
      v_4453 <- eval (handleImmediateWithSignExtend v_2541 8 8);
      v_4455 <- getRegister v_2543;
      v_4457 <- eval (add (concat (expression.bv_nat 1 0) v_4453) (concat (expression.bv_nat 1 0) v_4455));
      v_4459 <- eval (extract v_4457 1 2);
      v_4464 <- eval (extract v_4457 1 9);
      v_4468 <- eval (eq (extract v_4453 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2543) v_4464;
      setRegister of (mux (bit_and (eq v_4468 (eq (extract v_4455 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4468 (eq v_4459 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_4464);
      setRegister zf (zeroFlag v_4464);
      setRegister af (bv_xor (extract (bv_xor v_4453 v_4455) 3 4) (extract v_4457 4 5));
      setRegister sf v_4459;
      setRegister cf (extract v_4457 0 1);
      pure ()
    pat_end;
    pattern fun (v_2551 : reg (bv 8)) (v_2552 : reg (bv 8)) => do
      v_4488 <- getRegister v_2551;
      v_4490 <- getRegister v_2552;
      v_4492 <- eval (add (concat (expression.bv_nat 1 0) v_4488) (concat (expression.bv_nat 1 0) v_4490));
      v_4494 <- eval (extract v_4492 1 2);
      v_4499 <- eval (extract v_4492 1 9);
      v_4503 <- eval (eq (extract v_4488 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2552) v_4499;
      setRegister of (mux (bit_and (eq v_4503 (eq (extract v_4490 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4503 (eq v_4494 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_4499);
      setRegister zf (zeroFlag v_4499);
      setRegister af (bv_xor (extract (bv_xor v_4488 v_4490) 3 4) (extract v_4492 4 5));
      setRegister sf v_4494;
      setRegister cf (extract v_4492 0 1);
      pure ()
    pat_end;
    pattern fun (v_2560 : imm int) (v_2562 : reg (bv 8)) => do
      v_4550 <- eval (handleImmediateWithSignExtend v_2560 8 8);
      v_4552 <- getRegister v_2562;
      v_4554 <- eval (add (concat (expression.bv_nat 1 0) v_4550) (concat (expression.bv_nat 1 0) v_4552));
      v_4556 <- eval (extract v_4554 1 2);
      v_4557 <- eval (extract v_4554 1 9);
      v_4565 <- eval (eq (extract v_4550 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2562) v_4557;
      setRegister of (mux (bit_and (eq v_4565 (eq (extract v_4552 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4565 (eq v_4556 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_4557);
      setRegister af (bv_xor (extract (bv_xor v_4550 v_4552) 3 4) (extract v_4554 4 5));
      setRegister zf (zeroFlag v_4557);
      setRegister sf v_4556;
      setRegister cf (extract v_4554 0 1);
      pure ()
    pat_end;
    pattern fun (v_2571 : reg (bv 8)) (v_2570 : reg (bv 8)) => do
      v_4585 <- getRegister v_2571;
      v_4587 <- getRegister v_2570;
      v_4589 <- eval (add (concat (expression.bv_nat 1 0) v_4585) (concat (expression.bv_nat 1 0) v_4587));
      v_4591 <- eval (extract v_4589 1 2);
      v_4592 <- eval (extract v_4589 1 9);
      v_4600 <- eval (eq (extract v_4585 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2570) v_4592;
      setRegister of (mux (bit_and (eq v_4600 (eq (extract v_4587 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4600 (eq v_4591 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_4592);
      setRegister af (bv_xor (extract (bv_xor v_4585 v_4587) 3 4) (extract v_4589 4 5));
      setRegister zf (zeroFlag v_4592);
      setRegister sf v_4591;
      setRegister cf (extract v_4589 0 1);
      pure ()
    pat_end;
    pattern fun (v_2546 : Mem) (v_2547 : reg (bv 8)) => do
      v_9142 <- evaluateAddress v_2546;
      v_9143 <- load v_9142 1;
      v_9145 <- getRegister v_2547;
      v_9147 <- eval (add (concat (expression.bv_nat 1 0) v_9143) (concat (expression.bv_nat 1 0) v_9145));
      v_9149 <- eval (extract v_9147 1 2);
      v_9154 <- eval (extract v_9147 1 9);
      v_9158 <- eval (eq (extract v_9143 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2547) v_9154;
      setRegister of (mux (bit_and (eq v_9158 (eq (extract v_9145 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_9158 (eq v_9149 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_9154);
      setRegister zf (zeroFlag v_9154);
      setRegister af (bv_xor (extract (bv_xor v_9143 v_9145) 3 4) (extract v_9147 4 5));
      setRegister sf v_9149;
      setRegister cf (extract v_9147 0 1);
      pure ()
    pat_end;
    pattern fun (v_2530 : imm int) (v_2529 : Mem) => do
      v_10857 <- evaluateAddress v_2529;
      v_10858 <- eval (handleImmediateWithSignExtend v_2530 8 8);
      v_10860 <- load v_10857 1;
      v_10862 <- eval (add (concat (expression.bv_nat 1 0) v_10858) (concat (expression.bv_nat 1 0) v_10860));
      v_10863 <- eval (extract v_10862 1 9);
      store v_10857 v_10863 1;
      v_10866 <- eval (extract v_10862 1 2);
      v_10874 <- eval (eq (extract v_10858 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10874 (eq (extract v_10860 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10874 (eq v_10866 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_10863);
      setRegister af (bv_xor (extract (bv_xor v_10858 v_10860) 3 4) (extract v_10862 4 5));
      setRegister zf (zeroFlag v_10863);
      setRegister sf v_10866;
      setRegister cf (extract v_10862 0 1);
      pure ()
    pat_end;
    pattern fun (v_2534 : reg (bv 8)) (v_2533 : Mem) => do
      v_10889 <- evaluateAddress v_2533;
      v_10890 <- getRegister v_2534;
      v_10892 <- load v_10889 1;
      v_10894 <- eval (add (concat (expression.bv_nat 1 0) v_10890) (concat (expression.bv_nat 1 0) v_10892));
      v_10895 <- eval (extract v_10894 1 9);
      store v_10889 v_10895 1;
      v_10898 <- eval (extract v_10894 1 2);
      v_10906 <- eval (eq (extract v_10890 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10906 (eq (extract v_10892 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10906 (eq v_10898 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_10895);
      setRegister af (bv_xor (extract (bv_xor v_10890 v_10892) 3 4) (extract v_10894 4 5));
      setRegister zf (zeroFlag v_10895);
      setRegister sf v_10898;
      setRegister cf (extract v_10894 0 1);
      pure ()
    pat_end
