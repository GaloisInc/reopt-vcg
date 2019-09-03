def vmovsd1 : instruction :=
  definst "vmovsd" $ do
    pattern fun (v_2969 : reg (bv 128)) (v_2970 : reg (bv 128)) (v_2971 : reg (bv 128)) => do
      v_5348 <- getRegister v_2970;
      v_5350 <- getRegister v_2969;
      setRegister (lhs.of_reg v_2971) (concat (extract v_5348 0 64) (extract v_5350 64 128));
      pure ()
    pat_end;
    pattern fun (v_2965 : Mem) (v_2966 : reg (bv 128)) => do
      v_11156 <- evaluateAddress v_2965;
      v_11157 <- load v_11156 8;
      setRegister (lhs.of_reg v_2966) (concat (expression.bv_nat 64 0) v_11157);
      pure ()
    pat_end;
    pattern fun (v_2962 : reg (bv 128)) (v_2961 : Mem) => do
      v_13648 <- evaluateAddress v_2961;
      v_13649 <- getRegister v_2962;
      store v_13648 (extract v_13649 64 128) 8;
      pure ()
    pat_end
