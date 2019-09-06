def vsubss1 : instruction :=
  definst "vsubss" $ do
    pattern fun (v_3162 : reg (bv 128)) (v_3163 : reg (bv 128)) (v_3164 : reg (bv 128)) => do
      v_7299 <- getRegister v_3163;
      v_7303 <- getRegister v_3162;
      setRegister (lhs.of_reg v_3164) (concat (extract v_7299 0 96) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7299 96 128) 24 8) (MInt2Float (extract v_7303 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3156 : Mem) (v_3157 : reg (bv 128)) (v_3158 : reg (bv 128)) => do
      v_13204 <- getRegister v_3157;
      v_13208 <- evaluateAddress v_3156;
      v_13209 <- load v_13208 4;
      setRegister (lhs.of_reg v_3158) (concat (extract v_13204 0 96) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13204 96 128) 24 8) (MInt2Float v_13209 24 8)) 32));
      pure ()
    pat_end
