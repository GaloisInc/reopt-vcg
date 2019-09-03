def vmovq1 : instruction :=
  definst "vmovq" $ do
    pattern fun (v_2931 : reg (bv 128)) (v_2929 : reg (bv 64)) => do
      v_4953 <- getRegister v_2931;
      setRegister (lhs.of_reg v_2929) (extract v_4953 64 128);
      pure ()
    pat_end;
    pattern fun (v_2938 : reg (bv 64)) (v_2940 : reg (bv 128)) => do
      v_4960 <- getRegister v_2938;
      setRegister (lhs.of_reg v_2940) (concat (expression.bv_nat 64 0) v_4960);
      pure ()
    pat_end;
    pattern fun (v_2944 : reg (bv 128)) (v_2945 : reg (bv 128)) => do
      v_4963 <- getRegister v_2944;
      setRegister (lhs.of_reg v_2945) (concat (expression.bv_nat 64 0) (extract v_4963 64 128));
      pure ()
    pat_end;
    pattern fun (v_2926 : reg (bv 128)) (v_2925 : Mem) => do
      v_9496 <- evaluateAddress v_2925;
      v_9497 <- getRegister v_2926;
      store v_9496 (extract v_9497 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2934 : Mem) (v_2935 : reg (bv 128)) => do
      v_10346 <- evaluateAddress v_2934;
      v_10347 <- load v_10346 8;
      setRegister (lhs.of_reg v_2935) (concat (expression.bv_nat 64 0) v_10347);
      pure ()
    pat_end
