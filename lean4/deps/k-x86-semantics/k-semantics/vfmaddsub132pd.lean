def vfmaddsub132pd1 : instruction :=
  definst "vfmaddsub132pd" $ do
    pattern fun (v_2681 : reg (bv 128)) (v_2682 : reg (bv 128)) (v_2683 : reg (bv 128)) => do
      v_4840 <- getRegister v_2683;
      v_4842 <- getRegister v_2682;
      v_4844 <- getRegister v_2681;
      setRegister (lhs.of_reg v_2683) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4840 0 64) (extract v_4842 0 64) (extract v_4844 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4840 64 128) 53 11) (MInt2Float (extract v_4844 64 128) 53 11)) (MInt2Float (extract v_4842 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2691 : reg (bv 256)) (v_2692 : reg (bv 256)) (v_2693 : reg (bv 256)) => do
      v_4863 <- getRegister v_2693;
      v_4865 <- getRegister v_2692;
      v_4867 <- getRegister v_2691;
      setRegister (lhs.of_reg v_2693) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4863 0 64) (extract v_4865 0 64) (extract v_4867 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4863 64 128) 53 11) (MInt2Float (extract v_4867 64 128) 53 11)) (MInt2Float (extract v_4865 64 128) 53 11)) 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4863 128 192) (extract v_4865 128 192) (extract v_4867 128 192)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4863 192 256) 53 11) (MInt2Float (extract v_4867 192 256) 53 11)) (MInt2Float (extract v_4865 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2675 : Mem) (v_2676 : reg (bv 128)) (v_2677 : reg (bv 128)) => do
      v_10796 <- getRegister v_2677;
      v_10798 <- getRegister v_2676;
      v_10800 <- evaluateAddress v_2675;
      v_10801 <- load v_10800 16;
      setRegister (lhs.of_reg v_2677) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10796 0 64) (extract v_10798 0 64) (extract v_10801 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10796 64 128) 53 11) (MInt2Float (extract v_10801 64 128) 53 11)) (MInt2Float (extract v_10798 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2686 : Mem) (v_2687 : reg (bv 256)) (v_2688 : reg (bv 256)) => do
      v_10815 <- getRegister v_2688;
      v_10817 <- getRegister v_2687;
      v_10819 <- evaluateAddress v_2686;
      v_10820 <- load v_10819 32;
      setRegister (lhs.of_reg v_2688) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10815 0 64) (extract v_10817 0 64) (extract v_10820 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10815 64 128) 53 11) (MInt2Float (extract v_10820 64 128) 53 11)) (MInt2Float (extract v_10817 64 128) 53 11)) 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10815 128 192) (extract v_10817 128 192) (extract v_10820 128 192)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10815 192 256) 53 11) (MInt2Float (extract v_10820 192 256) 53 11)) (MInt2Float (extract v_10817 192 256) 53 11)) 64)));
      pure ()
    pat_end
