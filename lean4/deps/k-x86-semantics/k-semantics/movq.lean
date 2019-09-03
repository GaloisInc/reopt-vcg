def movq1 : instruction :=
  definst "movq" $ do
    pattern fun (v_2582 : imm int) (v_2583 : reg (bv 64)) => do
      setRegister (lhs.of_reg v_2583) (handleImmediateWithSignExtend v_2582 64 64);
      pure ()
    pat_end;
    pattern fun (v_2591 : reg (bv 64)) (v_2592 : reg (bv 64)) => do
      v_4017 <- getRegister v_2591;
      setRegister (lhs.of_reg v_2592) v_4017;
      pure ()
    pat_end;
    pattern fun (v_2596 : reg (bv 128)) (v_2597 : reg (bv 64)) => do
      v_4019 <- getRegister v_2596;
      setRegister (lhs.of_reg v_2597) (extract v_4019 64 128);
      pure ()
    pat_end;
    pattern fun (v_2606 : reg (bv 64)) (v_2605 : reg (bv 128)) => do
      v_4026 <- getRegister v_2606;
      setRegister (lhs.of_reg v_2605) (concat (expression.bv_nat 64 0) v_4026);
      pure ()
    pat_end;
    pattern fun (v_2610 : reg (bv 128)) (v_2611 : reg (bv 128)) => do
      v_4029 <- getRegister v_2610;
      setRegister (lhs.of_reg v_2611) (concat (expression.bv_nat 64 0) (extract v_4029 64 128));
      pure ()
    pat_end;
    pattern fun (v_2571 : imm int) (v_2570 : Mem) => do
      v_8610 <- evaluateAddress v_2570;
      store v_8610 (leanSignExtend (handleImmediateWithSignExtend v_2571 32 32) 64) 8;
      pure ()
    pat_end;
    pattern fun (v_2575 : reg (bv 64)) (v_2574 : Mem) => do
      v_8614 <- evaluateAddress v_2574;
      v_8615 <- getRegister v_2575;
      store v_8614 v_8615 8;
      pure ()
    pat_end;
    pattern fun (v_2579 : reg (bv 128)) (v_2578 : Mem) => do
      v_8617 <- evaluateAddress v_2578;
      v_8618 <- getRegister v_2579;
      store v_8617 (extract v_8618 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2587 : Mem) (v_2588 : reg (bv 64)) => do
      v_8858 <- evaluateAddress v_2587;
      v_8859 <- load v_8858 8;
      setRegister (lhs.of_reg v_2588) v_8859;
      pure ()
    pat_end;
    pattern fun (v_2601 : Mem) (v_2602 : reg (bv 128)) => do
      v_8861 <- evaluateAddress v_2601;
      v_8862 <- load v_8861 8;
      setRegister (lhs.of_reg v_2602) (concat (expression.bv_nat 64 0) v_8862);
      pure ()
    pat_end
