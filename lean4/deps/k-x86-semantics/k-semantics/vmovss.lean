def vmovss1 : instruction :=
  definst "vmovss" $ do
    pattern fun (v_3019 : reg (bv 128)) (v_3020 : reg (bv 128)) (v_3021 : reg (bv 128)) => do
      v_5418 <- getRegister v_3020;
      v_5420 <- getRegister v_3019;
      setRegister (lhs.of_reg v_3021) (concat (extract v_5418 0 96) (extract v_5420 96 128));
      pure ()
    pat_end;
    pattern fun (v_3015 : Mem) (v_3016 : reg (bv 128)) => do
      v_11205 <- evaluateAddress v_3015;
      v_11206 <- load v_11205 4;
      setRegister (lhs.of_reg v_3016) (concat (expression.bv_nat 96 0) v_11206);
      pure ()
    pat_end;
    pattern fun (v_3012 : reg (bv 128)) (v_3011 : Mem) => do
      v_13652 <- evaluateAddress v_3011;
      v_13653 <- getRegister v_3012;
      store v_13652 (extract v_13653 96 128) 4;
      pure ()
    pat_end
