def vfnmadd231sd1 : instruction :=
  definst "vfnmadd231sd" $ do
    pattern fun (v_3267 : reg (bv 128)) (v_3268 : reg (bv 128)) (v_3269 : reg (bv 128)) => do
      v_10974 <- getRegister v_3269;
      v_10977 <- getRegister v_3268;
      v_10979 <- getRegister v_3267;
      setRegister (lhs.of_reg v_3269) (concat (extract v_10974 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd231_double (extract v_10974 64 128) (extract v_10977 64 128) (extract v_10979 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3264 : Mem) (v_3262 : reg (bv 128)) (v_3263 : reg (bv 128)) => do
      v_21603 <- getRegister v_3263;
      v_21606 <- getRegister v_3262;
      v_21608 <- evaluateAddress v_3264;
      v_21609 <- load v_21608 8;
      setRegister (lhs.of_reg v_3263) (concat (extract v_21603 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd231_double (extract v_21603 64 128) (extract v_21606 64 128) v_21609));
      pure ()
    pat_end
