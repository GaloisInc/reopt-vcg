def vfmsub231ss1 : instruction :=
  definst "vfmsub231ss" $ do
    pattern fun (v_3000 : reg (bv 128)) (v_3001 : reg (bv 128)) (v_3002 : reg (bv 128)) => do
      v_6200 <- getRegister v_3002;
      v_6202 <- getRegister v_3001;
      v_6205 <- getRegister v_3000;
      setRegister (lhs.of_reg v_3002) (concat (extract v_6200 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6202 96 128) 24 8) (MInt2Float (extract v_6205 96 128) 24 8)) (MInt2Float (extract v_6200 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2994 : Mem) (v_2995 : reg (bv 128)) (v_2996 : reg (bv 128)) => do
      v_12035 <- getRegister v_2996;
      v_12037 <- getRegister v_2995;
      v_12040 <- evaluateAddress v_2994;
      v_12041 <- load v_12040 4;
      setRegister (lhs.of_reg v_2996) (concat (extract v_12035 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12037 96 128) 24 8) (MInt2Float v_12041 24 8)) (MInt2Float (extract v_12035 96 128) 24 8)) 32));
      pure ()
    pat_end
