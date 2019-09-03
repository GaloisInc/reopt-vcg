def subsd1 : instruction :=
  definst "subsd" $ do
    pattern fun (v_3223 : reg (bv 128)) (v_3224 : reg (bv 128)) => do
      v_7429 <- getRegister v_3224;
      v_7433 <- getRegister v_3223;
      setRegister (lhs.of_reg v_3224) (concat (extract v_7429 0 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7429 64 128) 53 11) (MInt2Float (extract v_7433 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3218 : Mem) (v_3219 : reg (bv 128)) => do
      v_10510 <- getRegister v_3219;
      v_10514 <- evaluateAddress v_3218;
      v_10515 <- load v_10514 8;
      setRegister (lhs.of_reg v_3219) (concat (extract v_10510 0 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_10510 64 128) 53 11) (MInt2Float v_10515 53 11)) 64));
      pure ()
    pat_end
