def vmovq1 : instruction :=
  definst "vmovq" $ do
    pattern fun (v_3019 : reg (bv 128)) (v_3018 : reg (bv 64)) => do
      v_5038 <- getRegister v_3019;
      setRegister (lhs.of_reg v_3018) (extract v_5038 64 128);
      pure ()
    pat_end;
    pattern fun (v_3027 : reg (bv 64)) (v_3028 : reg (bv 128)) => do
      v_5045 <- getRegister v_3027;
      setRegister (lhs.of_reg v_3028) (concat (expression.bv_nat 64 0) v_5045);
      pure ()
    pat_end;
    pattern fun (v_3032 : reg (bv 128)) (v_3033 : reg (bv 128)) => do
      v_5048 <- getRegister v_3032;
      setRegister (lhs.of_reg v_3033) (concat (expression.bv_nat 64 0) (extract v_5048 64 128));
      pure ()
    pat_end;
    pattern fun (v_3015 : reg (bv 128)) (v_3014 : Mem) => do
      v_9413 <- evaluateAddress v_3014;
      v_9414 <- getRegister v_3015;
      store v_9413 (extract v_9414 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_3023 : Mem) (v_3024 : reg (bv 128)) => do
      v_10239 <- evaluateAddress v_3023;
      v_10240 <- load v_10239 8;
      setRegister (lhs.of_reg v_3024) (concat (expression.bv_nat 64 0) v_10240);
      pure ()
    pat_end
