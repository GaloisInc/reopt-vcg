def movq1 : instruction :=
  definst "movq" $ do
    pattern fun (v_2570 : imm int) (v_2571 : reg (bv 64)) => do
      setRegister (lhs.of_reg v_2571) (handleImmediateWithSignExtend v_2570 64 64);
      pure ()
    pat_end;
    pattern fun (v_2579 : reg (bv 64)) (v_2580 : reg (bv 64)) => do
      v_4004 <- getRegister v_2579;
      setRegister (lhs.of_reg v_2580) v_4004;
      pure ()
    pat_end;
    pattern fun (v_2584 : reg (bv 128)) (v_2585 : reg (bv 64)) => do
      v_4006 <- getRegister v_2584;
      setRegister (lhs.of_reg v_2585) (extract v_4006 64 128);
      pure ()
    pat_end;
    pattern fun (v_2594 : reg (bv 64)) (v_2593 : reg (bv 128)) => do
      v_4013 <- getRegister v_2594;
      setRegister (lhs.of_reg v_2593) (concat (expression.bv_nat 64 0) v_4013);
      pure ()
    pat_end;
    pattern fun (v_2598 : reg (bv 128)) (v_2599 : reg (bv 128)) => do
      v_4016 <- getRegister v_2598;
      setRegister (lhs.of_reg v_2599) (concat (expression.bv_nat 64 0) (extract v_4016 64 128));
      pure ()
    pat_end;
    pattern fun (v_2558 : imm int) (v_2557 : Mem) => do
      v_8630 <- evaluateAddress v_2557;
      store v_8630 (mi 64 (svalueMInt (handleImmediateWithSignExtend v_2558 32 32))) 8;
      pure ()
    pat_end;
    pattern fun (v_2562 : reg (bv 64)) (v_2561 : Mem) => do
      v_8635 <- evaluateAddress v_2561;
      v_8636 <- getRegister v_2562;
      store v_8635 v_8636 8;
      pure ()
    pat_end;
    pattern fun (v_2566 : reg (bv 128)) (v_2565 : Mem) => do
      v_8638 <- evaluateAddress v_2565;
      v_8639 <- getRegister v_2566;
      store v_8638 (extract v_8639 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2574 : Mem) (v_2575 : reg (bv 64)) => do
      v_8879 <- evaluateAddress v_2574;
      v_8880 <- load v_8879 8;
      setRegister (lhs.of_reg v_2575) v_8880;
      pure ()
    pat_end;
    pattern fun (v_2588 : Mem) (v_2589 : reg (bv 128)) => do
      v_8882 <- evaluateAddress v_2588;
      v_8883 <- load v_8882 8;
      setRegister (lhs.of_reg v_2589) (concat (expression.bv_nat 64 0) v_8883);
      pure ()
    pat_end
