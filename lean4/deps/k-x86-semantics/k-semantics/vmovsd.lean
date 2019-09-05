def vmovsd1 : instruction :=
  definst "vmovsd" $ do
    pattern fun (v_3020 : reg (bv 128)) (v_3021 : reg (bv 128)) (v_3022 : reg (bv 128)) => do
      v_5033 <- getRegister v_3021;
      v_5035 <- getRegister v_3020;
      setRegister (lhs.of_reg v_3022) (concat (extract v_5033 0 64) (extract v_5035 64 128));
      pure ()
    pat_end;
    pattern fun (v_3016 : Mem) (v_3017 : reg (bv 128)) => do
      v_10217 <- evaluateAddress v_3016;
      v_10218 <- load v_10217 8;
      setRegister (lhs.of_reg v_3017) (concat (expression.bv_nat 64 0) v_10218);
      pure ()
    pat_end;
    pattern fun (v_3013 : reg (bv 128)) (v_3012 : Mem) => do
      v_12451 <- evaluateAddress v_3012;
      v_12452 <- getRegister v_3013;
      store v_12451 (extract v_12452 64 128) 8;
      pure ()
    pat_end
