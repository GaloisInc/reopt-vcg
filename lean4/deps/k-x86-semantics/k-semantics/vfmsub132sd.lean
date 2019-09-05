def vfmsub132sd1 : instruction :=
  definst "vfmsub132sd" $ do
    pattern fun (v_2857 : reg (bv 128)) (v_2858 : reg (bv 128)) (v_2859 : reg (bv 128)) => do
      v_5673 <- getRegister v_2859;
      v_5677 <- getRegister v_2857;
      v_5681 <- getRegister v_2858;
      setRegister (lhs.of_reg v_2859) (concat (extract v_5673 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5673 64 128) 53 11) (MInt2Float (extract v_5677 64 128) 53 11)) (MInt2Float (extract v_5681 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2851 : Mem) (v_2852 : reg (bv 128)) (v_2853 : reg (bv 128)) => do
      v_11565 <- getRegister v_2853;
      v_11569 <- evaluateAddress v_2851;
      v_11570 <- load v_11569 8;
      v_11573 <- getRegister v_2852;
      setRegister (lhs.of_reg v_2853) (concat (extract v_11565 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11565 64 128) 53 11) (MInt2Float v_11570 53 11)) (MInt2Float (extract v_11573 64 128) 53 11)) 64));
      pure ()
    pat_end
