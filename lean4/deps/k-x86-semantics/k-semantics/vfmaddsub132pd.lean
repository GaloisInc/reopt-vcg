def vfmaddsub132pd1 : instruction :=
  definst "vfmaddsub132pd" $ do
    pattern fun (v_2705 : reg (bv 128)) (v_2706 : reg (bv 128)) (v_2707 : reg (bv 128)) => do
      v_4867 <- getRegister v_2707;
      v_4869 <- getRegister v_2706;
      v_4871 <- getRegister v_2705;
      setRegister (lhs.of_reg v_2707) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4867 0 64) (extract v_4869 0 64) (extract v_4871 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4867 64 128) 53 11) (MInt2Float (extract v_4871 64 128) 53 11)) (MInt2Float (extract v_4869 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2719 : reg (bv 256)) (v_2720 : reg (bv 256)) (v_2721 : reg (bv 256)) => do
      v_4890 <- getRegister v_2721;
      v_4892 <- getRegister v_2720;
      v_4894 <- getRegister v_2719;
      setRegister (lhs.of_reg v_2721) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4890 0 64) (extract v_4892 0 64) (extract v_4894 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4890 64 128) 53 11) (MInt2Float (extract v_4894 64 128) 53 11)) (MInt2Float (extract v_4892 64 128) 53 11)) 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4890 128 192) (extract v_4892 128 192) (extract v_4894 128 192)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4890 192 256) 53 11) (MInt2Float (extract v_4894 192 256) 53 11)) (MInt2Float (extract v_4892 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2702 : Mem) (v_2700 : reg (bv 128)) (v_2701 : reg (bv 128)) => do
      v_10823 <- getRegister v_2701;
      v_10825 <- getRegister v_2700;
      v_10827 <- evaluateAddress v_2702;
      v_10828 <- load v_10827 16;
      setRegister (lhs.of_reg v_2701) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10823 0 64) (extract v_10825 0 64) (extract v_10828 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10823 64 128) 53 11) (MInt2Float (extract v_10828 64 128) 53 11)) (MInt2Float (extract v_10825 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2711 : Mem) (v_2714 : reg (bv 256)) (v_2715 : reg (bv 256)) => do
      v_10842 <- getRegister v_2715;
      v_10844 <- getRegister v_2714;
      v_10846 <- evaluateAddress v_2711;
      v_10847 <- load v_10846 32;
      setRegister (lhs.of_reg v_2715) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10842 0 64) (extract v_10844 0 64) (extract v_10847 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10842 64 128) 53 11) (MInt2Float (extract v_10847 64 128) 53 11)) (MInt2Float (extract v_10844 64 128) 53 11)) 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10842 128 192) (extract v_10844 128 192) (extract v_10847 128 192)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10842 192 256) 53 11) (MInt2Float (extract v_10847 192 256) 53 11)) (MInt2Float (extract v_10844 192 256) 53 11)) 64)));
      pure ()
    pat_end
