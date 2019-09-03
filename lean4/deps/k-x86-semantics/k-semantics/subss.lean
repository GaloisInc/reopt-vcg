def subss1 : instruction :=
  definst "subss" $ do
    pattern fun (v_3232 : reg (bv 128)) (v_3233 : reg (bv 128)) => do
      v_7444 <- getRegister v_3233;
      v_7448 <- getRegister v_3232;
      setRegister (lhs.of_reg v_3233) (concat (extract v_7444 0 96) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7444 96 128) 24 8) (MInt2Float (extract v_7448 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3227 : Mem) (v_3228 : reg (bv 128)) => do
      v_10521 <- getRegister v_3228;
      v_10525 <- evaluateAddress v_3227;
      v_10526 <- load v_10525 4;
      setRegister (lhs.of_reg v_3228) (concat (extract v_10521 0 96) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_10521 96 128) 24 8) (MInt2Float v_10526 24 8)) 32));
      pure ()
    pat_end
