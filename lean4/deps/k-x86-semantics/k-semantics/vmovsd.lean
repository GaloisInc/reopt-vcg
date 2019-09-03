def vmovsd1 : instruction :=
  definst "vmovsd" $ do
    pattern fun (v_2957 : reg (bv 128)) (v_2958 : reg (bv 128)) (v_2959 : reg (bv 128)) => do
      v_4975 <- getRegister v_2958;
      v_4977 <- getRegister v_2957;
      setRegister (lhs.of_reg v_2959) (concat (extract v_4975 0 64) (extract v_4977 64 128));
      pure ()
    pat_end;
    pattern fun (v_2952 : Mem) (v_2953 : reg (bv 128)) => do
      v_10351 <- evaluateAddress v_2952;
      v_10352 <- load v_10351 8;
      setRegister (lhs.of_reg v_2953) (concat (expression.bv_nat 64 0) v_10352);
      pure ()
    pat_end;
    pattern fun (v_2949 : reg (bv 128)) (v_2948 : Mem) => do
      v_12771 <- evaluateAddress v_2948;
      v_12772 <- getRegister v_2949;
      store v_12771 (extract v_12772 64 128) 8;
      pure ()
    pat_end
