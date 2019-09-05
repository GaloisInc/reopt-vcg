def vsubsd1 : instruction :=
  definst "vsubsd" $ do
    pattern fun (v_3124 : reg (bv 128)) (v_3125 : reg (bv 128)) (v_3126 : reg (bv 128)) => do
      v_7256 <- getRegister v_3125;
      v_7260 <- getRegister v_3124;
      setRegister (lhs.of_reg v_3126) (concat (extract v_7256 0 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7256 64 128) 53 11) (MInt2Float (extract v_7260 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3118 : Mem) (v_3119 : reg (bv 128)) (v_3120 : reg (bv 128)) => do
      v_13166 <- getRegister v_3119;
      v_13170 <- evaluateAddress v_3118;
      v_13171 <- load v_13170 8;
      setRegister (lhs.of_reg v_3120) (concat (extract v_13166 0 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13166 64 128) 53 11) (MInt2Float v_13171 53 11)) 64));
      pure ()
    pat_end
