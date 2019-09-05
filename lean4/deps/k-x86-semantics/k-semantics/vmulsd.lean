def vmulsd1 : instruction :=
  definst "vmulsd" $ do
    pattern fun (v_3177 : reg (bv 128)) (v_3178 : reg (bv 128)) (v_3179 : reg (bv 128)) => do
      v_5308 <- getRegister v_3178;
      v_5312 <- getRegister v_3177;
      setRegister (lhs.of_reg v_3179) (concat (extract v_5308 0 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5308 64 128) 53 11) (MInt2Float (extract v_5312 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3172 : Mem) (v_3173 : reg (bv 128)) (v_3174 : reg (bv 128)) => do
      v_10424 <- getRegister v_3173;
      v_10428 <- evaluateAddress v_3172;
      v_10429 <- load v_10428 8;
      setRegister (lhs.of_reg v_3174) (concat (extract v_10424 0 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10424 64 128) 53 11) (MInt2Float v_10429 53 11)) 64));
      pure ()
    pat_end
