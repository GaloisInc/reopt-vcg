def vmulss1 : instruction :=
  definst "vmulss" $ do
    pattern fun (v_3125 : reg (bv 128)) (v_3126 : reg (bv 128)) (v_3127 : reg (bv 128)) => do
      v_5266 <- getRegister v_3126;
      v_5270 <- getRegister v_3125;
      setRegister (lhs.of_reg v_3127) (concat (extract v_5266 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5266 96 128) 24 8) (MInt2Float (extract v_5270 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3119 : Mem) (v_3120 : reg (bv 128)) (v_3121 : reg (bv 128)) => do
      v_10569 <- getRegister v_3120;
      v_10573 <- evaluateAddress v_3119;
      v_10574 <- load v_10573 4;
      setRegister (lhs.of_reg v_3121) (concat (extract v_10569 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10569 96 128) 24 8) (MInt2Float v_10574 24 8)) 32));
      pure ()
    pat_end
