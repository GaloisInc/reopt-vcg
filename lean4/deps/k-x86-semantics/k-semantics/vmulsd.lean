def vmulsd1 : instruction :=
  definst "vmulsd" $ do
    pattern fun (v_3202 : reg (bv 128)) (v_3203 : reg (bv 128)) (v_3204 : reg (bv 128)) => do
      v_5335 <- getRegister v_3203;
      v_5339 <- getRegister v_3202;
      setRegister (lhs.of_reg v_3204) (concat (extract v_5335 0 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5335 64 128) 53 11) (MInt2Float (extract v_5339 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3197 : Mem) (v_3198 : reg (bv 128)) (v_3199 : reg (bv 128)) => do
      v_10451 <- getRegister v_3198;
      v_10455 <- evaluateAddress v_3197;
      v_10456 <- load v_10455 8;
      setRegister (lhs.of_reg v_3199) (concat (extract v_10451 0 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10451 64 128) 53 11) (MInt2Float v_10456 53 11)) 64));
      pure ()
    pat_end
