def movq1 : instruction :=
  definst "movq" $ do
    pattern fun (v_2632 : imm int) (v_2633 : reg (bv 64)) => do
      setRegister (lhs.of_reg v_2633) (handleImmediateWithSignExtend v_2632 64 64);
      pure ()
    pat_end;
    pattern fun (v_2641 : reg (bv 64)) (v_2642 : reg (bv 64)) => do
      v_4068 <- getRegister v_2641;
      setRegister (lhs.of_reg v_2642) v_4068;
      pure ()
    pat_end;
    pattern fun (v_2648 : reg (bv 128)) (v_2646 : reg (bv 64)) => do
      v_4070 <- getRegister v_2648;
      setRegister (lhs.of_reg v_2646) (extract v_4070 64 128);
      pure ()
    pat_end;
    pattern fun (v_2655 : reg (bv 64)) (v_2657 : reg (bv 128)) => do
      v_4077 <- getRegister v_2655;
      setRegister (lhs.of_reg v_2657) (concat (expression.bv_nat 64 0) v_4077);
      pure ()
    pat_end;
    pattern fun (v_2661 : reg (bv 128)) (v_2662 : reg (bv 128)) => do
      v_4080 <- getRegister v_2661;
      setRegister (lhs.of_reg v_2662) (concat (expression.bv_nat 64 0) (extract v_4080 64 128));
      pure ()
    pat_end;
    pattern fun (v_2621 : imm int) (v_2620 : Mem) => do
      v_8474 <- evaluateAddress v_2620;
      store v_8474 (sext (handleImmediateWithSignExtend v_2621 32 32) 64) 8;
      pure ()
    pat_end;
    pattern fun (v_2625 : reg (bv 64)) (v_2624 : Mem) => do
      v_8478 <- evaluateAddress v_2624;
      v_8479 <- getRegister v_2625;
      store v_8478 v_8479 8;
      pure ()
    pat_end;
    pattern fun (v_2629 : reg (bv 128)) (v_2628 : Mem) => do
      v_8481 <- evaluateAddress v_2628;
      v_8482 <- getRegister v_2629;
      store v_8481 (extract v_8482 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2637 : Mem) (v_2638 : reg (bv 64)) => do
      v_8722 <- evaluateAddress v_2637;
      v_8723 <- load v_8722 8;
      setRegister (lhs.of_reg v_2638) v_8723;
      pure ()
    pat_end;
    pattern fun (v_2651 : Mem) (v_2652 : reg (bv 128)) => do
      v_8725 <- evaluateAddress v_2651;
      v_8726 <- load v_8725 8;
      setRegister (lhs.of_reg v_2652) (concat (expression.bv_nat 64 0) v_8726);
      pure ()
    pat_end
