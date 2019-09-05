def vaddsd1 : instruction :=
  definst "vaddsd" $ do
    pattern fun (v_2678 : reg (bv 128)) (v_2679 : reg (bv 128)) (v_2680 : reg (bv 128)) => do
      v_4939 <- getRegister v_2679;
      v_4943 <- getRegister v_2678;
      setRegister (lhs.of_reg v_2680) (concat (extract v_4939 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4939 64 128) 53 11) (MInt2Float (extract v_4943 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2672 : Mem) (v_2673 : reg (bv 128)) (v_2674 : reg (bv 128)) => do
      v_9232 <- getRegister v_2673;
      v_9236 <- evaluateAddress v_2672;
      v_9237 <- load v_9236 8;
      setRegister (lhs.of_reg v_2674) (concat (extract v_9232 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9232 64 128) 53 11) (MInt2Float v_9237 53 11)) 64));
      pure ()
    pat_end
