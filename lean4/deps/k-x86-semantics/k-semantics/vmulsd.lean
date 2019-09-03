def vmulsd1 : instruction :=
  definst "vmulsd" $ do
    pattern fun (v_3114 : reg (bv 128)) (v_3115 : reg (bv 128)) (v_3116 : reg (bv 128)) => do
      v_5250 <- getRegister v_3115;
      v_5254 <- getRegister v_3114;
      setRegister (lhs.of_reg v_3116) (concat (extract v_5250 0 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5250 64 128) 53 11) (MInt2Float (extract v_5254 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3108 : Mem) (v_3109 : reg (bv 128)) (v_3110 : reg (bv 128)) => do
      v_10558 <- getRegister v_3109;
      v_10562 <- evaluateAddress v_3108;
      v_10563 <- load v_10562 8;
      setRegister (lhs.of_reg v_3110) (concat (extract v_10558 0 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10558 64 128) 53 11) (MInt2Float v_10563 53 11)) 64));
      pure ()
    pat_end
