def vmovss1 : instruction :=
  definst "vmovss" $ do
    pattern fun (v_3095 : reg (bv 128)) (v_3096 : reg (bv 128)) (v_3097 : reg (bv 128)) => do
      v_5130 <- getRegister v_3096;
      v_5132 <- getRegister v_3095;
      setRegister (lhs.of_reg v_3097) (concat (extract v_5130 0 96) (extract v_5132 96 128));
      pure ()
    pat_end;
    pattern fun (v_3091 : Mem) (v_3092 : reg (bv 128)) => do
      v_10293 <- evaluateAddress v_3091;
      v_10294 <- load v_10293 4;
      setRegister (lhs.of_reg v_3092) (concat (expression.bv_nat 96 0) v_10294);
      pure ()
    pat_end;
    pattern fun (v_3088 : reg (bv 128)) (v_3087 : Mem) => do
      v_12482 <- evaluateAddress v_3087;
      v_12483 <- getRegister v_3088;
      store v_12482 (extract v_12483 96 128) 4;
      pure ()
    pat_end
