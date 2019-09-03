def vmovd1 : instruction :=
  definst "vmovd" $ do
    pattern fun (v_2723 : reg (bv 128)) (v_2722 : reg (bv 32)) => do
      v_4689 <- getRegister v_2723;
      setRegister (lhs.of_reg v_2722) (extract v_4689 96 128);
      pure ()
    pat_end;
    pattern fun (v_2731 : reg (bv 32)) (v_2732 : reg (bv 128)) => do
      v_4696 <- getRegister v_2731;
      setRegister (lhs.of_reg v_2732) (concat (expression.bv_nat 96 0) (concat (extract v_4696 0 8) (extract v_4696 8 32)));
      pure ()
    pat_end;
    pattern fun (v_2718 : reg (bv 128)) (v_2717 : Mem) => do
      v_9404 <- evaluateAddress v_2717;
      v_9405 <- getRegister v_2718;
      store v_9404 (extract v_9405 96 128) 4;
      pure ()
    pat_end;
    pattern fun (v_2726 : Mem) (v_2727 : reg (bv 128)) => do
      v_10274 <- evaluateAddress v_2726;
      v_10275 <- load v_10274 4;
      setRegister (lhs.of_reg v_2727) (concat (expression.bv_nat 96 0) (concat (extract v_10275 0 8) (extract v_10275 8 32)));
      pure ()
    pat_end
