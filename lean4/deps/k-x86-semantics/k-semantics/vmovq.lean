def vmovq1 : instruction :=
  definst "vmovq" $ do
    pattern fun (v_2993 : reg (bv 128)) (v_2994 : reg (bv 64)) => do
      v_5011 <- getRegister v_2993;
      setRegister (lhs.of_reg v_2994) (extract v_5011 64 128);
      pure ()
    pat_end;
    pattern fun (v_3003 : reg (bv 64)) (v_3002 : reg (bv 128)) => do
      v_5018 <- getRegister v_3003;
      setRegister (lhs.of_reg v_3002) (concat (expression.bv_nat 64 0) v_5018);
      pure ()
    pat_end;
    pattern fun (v_3007 : reg (bv 128)) (v_3008 : reg (bv 128)) => do
      v_5021 <- getRegister v_3007;
      setRegister (lhs.of_reg v_3008) (concat (expression.bv_nat 64 0) (extract v_5021 64 128));
      pure ()
    pat_end;
    pattern fun (v_2990 : reg (bv 128)) (v_2989 : Mem) => do
      v_9386 <- evaluateAddress v_2989;
      v_9387 <- getRegister v_2990;
      store v_9386 (extract v_9387 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2998 : Mem) (v_2999 : reg (bv 128)) => do
      v_10212 <- evaluateAddress v_2998;
      v_10213 <- load v_10212 8;
      setRegister (lhs.of_reg v_2999) (concat (expression.bv_nat 64 0) v_10213);
      pure ()
    pat_end
