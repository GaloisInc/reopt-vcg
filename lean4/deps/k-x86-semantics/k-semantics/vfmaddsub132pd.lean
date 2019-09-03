def vfmaddsub132pd1 : instruction :=
  definst "vfmaddsub132pd" $ do
    pattern fun (v_2616 : reg (bv 128)) (v_2617 : reg (bv 128)) (v_2618 : reg (bv 128)) => do
      v_4773 <- getRegister v_2618;
      v_4775 <- getRegister v_2617;
      v_4777 <- getRegister v_2616;
      setRegister (lhs.of_reg v_2618) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4773 0 64) (extract v_4775 0 64) (extract v_4777 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4773 64 128) 53 11) (MInt2Float (extract v_4777 64 128) 53 11)) (MInt2Float (extract v_4775 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2628 : reg (bv 256)) (v_2629 : reg (bv 256)) (v_2630 : reg (bv 256)) => do
      v_4796 <- getRegister v_2630;
      v_4798 <- getRegister v_2629;
      v_4800 <- getRegister v_2628;
      setRegister (lhs.of_reg v_2630) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4796 0 64) (extract v_4798 0 64) (extract v_4800 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4796 64 128) 53 11) (MInt2Float (extract v_4800 64 128) 53 11)) (MInt2Float (extract v_4798 64 128) 53 11)) 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4796 128 192) (extract v_4798 128 192) (extract v_4800 128 192)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4796 192 256) 53 11) (MInt2Float (extract v_4800 192 256) 53 11)) (MInt2Float (extract v_4798 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2613 : Mem) (v_2611 : reg (bv 128)) (v_2612 : reg (bv 128)) => do
      v_10712 <- getRegister v_2612;
      v_10714 <- getRegister v_2611;
      v_10716 <- evaluateAddress v_2613;
      v_10717 <- load v_10716 16;
      setRegister (lhs.of_reg v_2612) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10712 0 64) (extract v_10714 0 64) (extract v_10717 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10712 64 128) 53 11) (MInt2Float (extract v_10717 64 128) 53 11)) (MInt2Float (extract v_10714 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2622 : Mem) (v_2623 : reg (bv 256)) (v_2624 : reg (bv 256)) => do
      v_10731 <- getRegister v_2624;
      v_10733 <- getRegister v_2623;
      v_10735 <- evaluateAddress v_2622;
      v_10736 <- load v_10735 32;
      setRegister (lhs.of_reg v_2624) (concat (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10731 0 64) (extract v_10733 0 64) (extract v_10736 0 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10731 64 128) 53 11) (MInt2Float (extract v_10736 64 128) 53 11)) (MInt2Float (extract v_10733 64 128) 53 11)) 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10731 128 192) (extract v_10733 128 192) (extract v_10736 128 192)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10731 192 256) 53 11) (MInt2Float (extract v_10736 192 256) 53 11)) (MInt2Float (extract v_10733 192 256) 53 11)) 64)));
      pure ()
    pat_end
