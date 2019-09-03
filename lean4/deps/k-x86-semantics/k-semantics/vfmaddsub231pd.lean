def vfmaddsub231pd1 : instruction :=
  definst "vfmaddsub231pd" $ do
    pattern fun (v_2717 : reg (bv 128)) (v_2718 : reg (bv 128)) (v_2719 : reg (bv 128)) => do
      v_6634 <- getRegister v_2718;
      v_6635 <- eval (extract v_6634 0 64);
      v_6643 <- getRegister v_2717;
      v_6644 <- eval (extract v_6643 0 64);
      v_6653 <- getRegister v_2719;
      v_6654 <- eval (extract v_6653 0 64);
      v_6664 <- eval (extract v_6634 64 128);
      v_6672 <- eval (extract v_6643 64 128);
      v_6681 <- eval (extract v_6653 64 128);
      setRegister (lhs.of_reg v_2719) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6635 0 1)) (uvalueMInt (extract v_6635 1 12)) (uvalueMInt (extract v_6635 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6644 0 1)) (uvalueMInt (extract v_6644 1 12)) (uvalueMInt (extract v_6644 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6654 0 1)) (uvalueMInt (extract v_6654 1 12)) (uvalueMInt (extract v_6654 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6664 0 1)) (uvalueMInt (extract v_6664 1 12)) (uvalueMInt (extract v_6664 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6672 0 1)) (uvalueMInt (extract v_6672 1 12)) (uvalueMInt (extract v_6672 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6681 0 1)) (uvalueMInt (extract v_6681 1 12)) (uvalueMInt (extract v_6681 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2728 : reg (bv 256)) (v_2729 : reg (bv 256)) (v_2730 : reg (bv 256)) => do
      v_6698 <- getRegister v_2729;
      v_6699 <- eval (extract v_6698 0 64);
      v_6707 <- getRegister v_2728;
      v_6708 <- eval (extract v_6707 0 64);
      v_6717 <- getRegister v_2730;
      v_6718 <- eval (extract v_6717 0 64);
      v_6728 <- eval (extract v_6698 64 128);
      v_6736 <- eval (extract v_6707 64 128);
      v_6745 <- eval (extract v_6717 64 128);
      v_6756 <- eval (extract v_6698 128 192);
      v_6764 <- eval (extract v_6707 128 192);
      v_6773 <- eval (extract v_6717 128 192);
      v_6783 <- eval (extract v_6698 192 256);
      v_6791 <- eval (extract v_6707 192 256);
      v_6800 <- eval (extract v_6717 192 256);
      setRegister (lhs.of_reg v_2730) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6699 0 1)) (uvalueMInt (extract v_6699 1 12)) (uvalueMInt (extract v_6699 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6708 0 1)) (uvalueMInt (extract v_6708 1 12)) (uvalueMInt (extract v_6708 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6718 0 1)) (uvalueMInt (extract v_6718 1 12)) (uvalueMInt (extract v_6718 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6728 0 1)) (uvalueMInt (extract v_6728 1 12)) (uvalueMInt (extract v_6728 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6736 0 1)) (uvalueMInt (extract v_6736 1 12)) (uvalueMInt (extract v_6736 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6745 0 1)) (uvalueMInt (extract v_6745 1 12)) (uvalueMInt (extract v_6745 12 64)))) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6756 0 1)) (uvalueMInt (extract v_6756 1 12)) (uvalueMInt (extract v_6756 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6764 0 1)) (uvalueMInt (extract v_6764 1 12)) (uvalueMInt (extract v_6764 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6773 0 1)) (uvalueMInt (extract v_6773 1 12)) (uvalueMInt (extract v_6773 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6783 0 1)) (uvalueMInt (extract v_6783 1 12)) (uvalueMInt (extract v_6783 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6791 0 1)) (uvalueMInt (extract v_6791 1 12)) (uvalueMInt (extract v_6791 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6800 0 1)) (uvalueMInt (extract v_6800 1 12)) (uvalueMInt (extract v_6800 12 64)))) 64)));
      pure ()
    pat_end;
    pattern fun (v_2714 : Mem) (v_2712 : reg (bv 128)) (v_2713 : reg (bv 128)) => do
      v_17473 <- getRegister v_2712;
      v_17474 <- eval (extract v_17473 0 64);
      v_17482 <- evaluateAddress v_2714;
      v_17483 <- load v_17482 16;
      v_17484 <- eval (extract v_17483 0 64);
      v_17493 <- getRegister v_2713;
      v_17494 <- eval (extract v_17493 0 64);
      v_17504 <- eval (extract v_17473 64 128);
      v_17512 <- eval (extract v_17483 64 128);
      v_17521 <- eval (extract v_17493 64 128);
      setRegister (lhs.of_reg v_2713) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17474 0 1)) (uvalueMInt (extract v_17474 1 12)) (uvalueMInt (extract v_17474 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17484 0 1)) (uvalueMInt (extract v_17484 1 12)) (uvalueMInt (extract v_17484 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17494 0 1)) (uvalueMInt (extract v_17494 1 12)) (uvalueMInt (extract v_17494 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17504 0 1)) (uvalueMInt (extract v_17504 1 12)) (uvalueMInt (extract v_17504 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17512 0 1)) (uvalueMInt (extract v_17512 1 12)) (uvalueMInt (extract v_17512 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17521 0 1)) (uvalueMInt (extract v_17521 1 12)) (uvalueMInt (extract v_17521 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2723 : Mem) (v_2724 : reg (bv 256)) (v_2725 : reg (bv 256)) => do
      v_17533 <- getRegister v_2724;
      v_17534 <- eval (extract v_17533 0 64);
      v_17542 <- evaluateAddress v_2723;
      v_17543 <- load v_17542 32;
      v_17544 <- eval (extract v_17543 0 64);
      v_17553 <- getRegister v_2725;
      v_17554 <- eval (extract v_17553 0 64);
      v_17564 <- eval (extract v_17533 64 128);
      v_17572 <- eval (extract v_17543 64 128);
      v_17581 <- eval (extract v_17553 64 128);
      v_17592 <- eval (extract v_17533 128 192);
      v_17600 <- eval (extract v_17543 128 192);
      v_17609 <- eval (extract v_17553 128 192);
      v_17619 <- eval (extract v_17533 192 256);
      v_17627 <- eval (extract v_17543 192 256);
      v_17636 <- eval (extract v_17553 192 256);
      setRegister (lhs.of_reg v_2725) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17534 0 1)) (uvalueMInt (extract v_17534 1 12)) (uvalueMInt (extract v_17534 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17544 0 1)) (uvalueMInt (extract v_17544 1 12)) (uvalueMInt (extract v_17544 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17554 0 1)) (uvalueMInt (extract v_17554 1 12)) (uvalueMInt (extract v_17554 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17564 0 1)) (uvalueMInt (extract v_17564 1 12)) (uvalueMInt (extract v_17564 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17572 0 1)) (uvalueMInt (extract v_17572 1 12)) (uvalueMInt (extract v_17572 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17581 0 1)) (uvalueMInt (extract v_17581 1 12)) (uvalueMInt (extract v_17581 12 64)))) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17592 0 1)) (uvalueMInt (extract v_17592 1 12)) (uvalueMInt (extract v_17592 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17600 0 1)) (uvalueMInt (extract v_17600 1 12)) (uvalueMInt (extract v_17600 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17609 0 1)) (uvalueMInt (extract v_17609 1 12)) (uvalueMInt (extract v_17609 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17619 0 1)) (uvalueMInt (extract v_17619 1 12)) (uvalueMInt (extract v_17619 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17627 0 1)) (uvalueMInt (extract v_17627 1 12)) (uvalueMInt (extract v_17627 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_17636 0 1)) (uvalueMInt (extract v_17636 1 12)) (uvalueMInt (extract v_17636 12 64)))) 64)));
      pure ()
    pat_end
