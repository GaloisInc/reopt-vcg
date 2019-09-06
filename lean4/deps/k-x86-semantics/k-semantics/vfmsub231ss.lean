def vfmsub231ss1 : instruction :=
  definst "vfmsub231ss" $ do
    pattern fun (v_3024 : reg (bv 128)) (v_3025 : reg (bv 128)) (v_3026 : reg (bv 128)) => do
      v_6227 <- getRegister v_3026;
      v_6229 <- getRegister v_3025;
      v_6232 <- getRegister v_3024;
      setRegister (lhs.of_reg v_3026) (concat (extract v_6227 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6229 96 128) 24 8) (MInt2Float (extract v_6232 96 128) 24 8)) (MInt2Float (extract v_6227 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3021 : Mem) (v_3019 : reg (bv 128)) (v_3020 : reg (bv 128)) => do
      v_12062 <- getRegister v_3020;
      v_12064 <- getRegister v_3019;
      v_12067 <- evaluateAddress v_3021;
      v_12068 <- load v_12067 4;
      setRegister (lhs.of_reg v_3020) (concat (extract v_12062 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12064 96 128) 24 8) (MInt2Float v_12068 24 8)) (MInt2Float (extract v_12062 96 128) 24 8)) 32));
      pure ()
    pat_end
