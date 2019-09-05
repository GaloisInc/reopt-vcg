def vfmsub132ss1 : instruction :=
  definst "vfmsub132ss" $ do
    pattern fun (v_2868 : reg (bv 128)) (v_2869 : reg (bv 128)) (v_2870 : reg (bv 128)) => do
      v_5693 <- getRegister v_2870;
      v_5697 <- getRegister v_2868;
      v_5701 <- getRegister v_2869;
      setRegister (lhs.of_reg v_2870) (concat (extract v_5693 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5693 96 128) 24 8) (MInt2Float (extract v_5697 96 128) 24 8)) (MInt2Float (extract v_5701 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2862 : Mem) (v_2863 : reg (bv 128)) (v_2864 : reg (bv 128)) => do
      v_11580 <- getRegister v_2864;
      v_11584 <- evaluateAddress v_2862;
      v_11585 <- load v_11584 4;
      v_11588 <- getRegister v_2863;
      setRegister (lhs.of_reg v_2864) (concat (extract v_11580 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11580 96 128) 24 8) (MInt2Float v_11585 24 8)) (MInt2Float (extract v_11588 96 128) 24 8)) 32));
      pure ()
    pat_end
