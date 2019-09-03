def vfmaddsub213pd1 : instruction :=
  definst "vfmaddsub213pd" $ do
    pattern fun (v_2660 : reg (bv 128)) (v_2661 : reg (bv 128)) (v_2662 : reg (bv 128)) => do
      v_4970 <- getRegister v_2661;
      v_4973 <- getRegister v_2662;
      v_4977 <- getRegister v_2660;
      setRegister (lhs.of_reg v_2662) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4970 0 64) 53 11) (MInt2Float (extract v_4973 0 64) 53 11)) (MInt2Float (extract v_4977 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4970 64 128) 53 11) (MInt2Float (extract v_4973 64 128) 53 11)) (MInt2Float (extract v_4977 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2672 : reg (bv 256)) (v_2673 : reg (bv 256)) (v_2674 : reg (bv 256)) => do
      v_4998 <- getRegister v_2673;
      v_5001 <- getRegister v_2674;
      v_5005 <- getRegister v_2672;
      setRegister (lhs.of_reg v_2674) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4998 0 64) 53 11) (MInt2Float (extract v_5001 0 64) 53 11)) (MInt2Float (extract v_5005 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4998 64 128) 53 11) (MInt2Float (extract v_5001 64 128) 53 11)) (MInt2Float (extract v_5005 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4998 128 192) 53 11) (MInt2Float (extract v_5001 128 192) 53 11)) (MInt2Float (extract v_5005 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4998 192 256) 53 11) (MInt2Float (extract v_5001 192 256) 53 11)) (MInt2Float (extract v_5005 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2657 : Mem) (v_2655 : reg (bv 128)) (v_2656 : reg (bv 128)) => do
      v_10893 <- getRegister v_2655;
      v_10896 <- getRegister v_2656;
      v_10900 <- evaluateAddress v_2657;
      v_10901 <- load v_10900 16;
      setRegister (lhs.of_reg v_2656) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10893 0 64) 53 11) (MInt2Float (extract v_10896 0 64) 53 11)) (MInt2Float (extract v_10901 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10893 64 128) 53 11) (MInt2Float (extract v_10896 64 128) 53 11)) (MInt2Float (extract v_10901 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2666 : Mem) (v_2667 : reg (bv 256)) (v_2668 : reg (bv 256)) => do
      v_10917 <- getRegister v_2667;
      v_10920 <- getRegister v_2668;
      v_10924 <- evaluateAddress v_2666;
      v_10925 <- load v_10924 32;
      setRegister (lhs.of_reg v_2668) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10917 0 64) 53 11) (MInt2Float (extract v_10920 0 64) 53 11)) (MInt2Float (extract v_10925 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10917 64 128) 53 11) (MInt2Float (extract v_10920 64 128) 53 11)) (MInt2Float (extract v_10925 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10917 128 192) 53 11) (MInt2Float (extract v_10920 128 192) 53 11)) (MInt2Float (extract v_10925 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10917 192 256) 53 11) (MInt2Float (extract v_10920 192 256) 53 11)) (MInt2Float (extract v_10925 192 256) 53 11)) 64)));
      pure ()
    pat_end
