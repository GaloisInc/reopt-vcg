def vfmsubadd213ps1 : instruction :=
  definst "vfmsubadd213ps" $ do
    pattern fun (v_3025 : reg (bv 128)) (v_3026 : reg (bv 128)) (v_3027 : reg (bv 128)) => do
      v_9660 <- getRegister v_3026;
      v_9661 <- eval (extract v_9660 0 32);
      v_9669 <- getRegister v_3027;
      v_9670 <- eval (extract v_9669 0 32);
      v_9679 <- getRegister v_3025;
      v_9680 <- eval (extract v_9679 0 32);
      v_9690 <- eval (extract v_9660 32 64);
      v_9698 <- eval (extract v_9669 32 64);
      v_9707 <- eval (extract v_9679 32 64);
      v_9718 <- eval (extract v_9660 64 96);
      v_9726 <- eval (extract v_9669 64 96);
      v_9735 <- eval (extract v_9679 64 96);
      v_9745 <- eval (extract v_9660 96 128);
      v_9753 <- eval (extract v_9669 96 128);
      v_9762 <- eval (extract v_9679 96 128);
      setRegister (lhs.of_reg v_3027) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9661 0 1)) (uvalueMInt (extract v_9661 1 9)) (uvalueMInt (extract v_9661 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9670 0 1)) (uvalueMInt (extract v_9670 1 9)) (uvalueMInt (extract v_9670 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9680 0 1)) (uvalueMInt (extract v_9680 1 9)) (uvalueMInt (extract v_9680 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9690 0 1)) (uvalueMInt (extract v_9690 1 9)) (uvalueMInt (extract v_9690 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9698 0 1)) (uvalueMInt (extract v_9698 1 9)) (uvalueMInt (extract v_9698 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9707 0 1)) (uvalueMInt (extract v_9707 1 9)) (uvalueMInt (extract v_9707 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9718 0 1)) (uvalueMInt (extract v_9718 1 9)) (uvalueMInt (extract v_9718 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9726 0 1)) (uvalueMInt (extract v_9726 1 9)) (uvalueMInt (extract v_9726 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9735 0 1)) (uvalueMInt (extract v_9735 1 9)) (uvalueMInt (extract v_9735 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9745 0 1)) (uvalueMInt (extract v_9745 1 9)) (uvalueMInt (extract v_9745 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9753 0 1)) (uvalueMInt (extract v_9753 1 9)) (uvalueMInt (extract v_9753 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9762 0 1)) (uvalueMInt (extract v_9762 1 9)) (uvalueMInt (extract v_9762 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_3036 : reg (bv 256)) (v_3037 : reg (bv 256)) (v_3038 : reg (bv 256)) => do
      v_9780 <- getRegister v_3037;
      v_9781 <- eval (extract v_9780 0 32);
      v_9789 <- getRegister v_3038;
      v_9790 <- eval (extract v_9789 0 32);
      v_9799 <- getRegister v_3036;
      v_9800 <- eval (extract v_9799 0 32);
      v_9810 <- eval (extract v_9780 32 64);
      v_9818 <- eval (extract v_9789 32 64);
      v_9827 <- eval (extract v_9799 32 64);
      v_9838 <- eval (extract v_9780 64 96);
      v_9846 <- eval (extract v_9789 64 96);
      v_9855 <- eval (extract v_9799 64 96);
      v_9865 <- eval (extract v_9780 96 128);
      v_9873 <- eval (extract v_9789 96 128);
      v_9882 <- eval (extract v_9799 96 128);
      v_9893 <- eval (extract v_9780 128 160);
      v_9901 <- eval (extract v_9789 128 160);
      v_9910 <- eval (extract v_9799 128 160);
      v_9920 <- eval (extract v_9780 160 192);
      v_9928 <- eval (extract v_9789 160 192);
      v_9937 <- eval (extract v_9799 160 192);
      v_9948 <- eval (extract v_9780 192 224);
      v_9956 <- eval (extract v_9789 192 224);
      v_9965 <- eval (extract v_9799 192 224);
      v_9975 <- eval (extract v_9780 224 256);
      v_9983 <- eval (extract v_9789 224 256);
      v_9992 <- eval (extract v_9799 224 256);
      setRegister (lhs.of_reg v_3038) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9781 0 1)) (uvalueMInt (extract v_9781 1 9)) (uvalueMInt (extract v_9781 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9790 0 1)) (uvalueMInt (extract v_9790 1 9)) (uvalueMInt (extract v_9790 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9800 0 1)) (uvalueMInt (extract v_9800 1 9)) (uvalueMInt (extract v_9800 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9810 0 1)) (uvalueMInt (extract v_9810 1 9)) (uvalueMInt (extract v_9810 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9818 0 1)) (uvalueMInt (extract v_9818 1 9)) (uvalueMInt (extract v_9818 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9827 0 1)) (uvalueMInt (extract v_9827 1 9)) (uvalueMInt (extract v_9827 9 32)))) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9838 0 1)) (uvalueMInt (extract v_9838 1 9)) (uvalueMInt (extract v_9838 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9846 0 1)) (uvalueMInt (extract v_9846 1 9)) (uvalueMInt (extract v_9846 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9855 0 1)) (uvalueMInt (extract v_9855 1 9)) (uvalueMInt (extract v_9855 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9865 0 1)) (uvalueMInt (extract v_9865 1 9)) (uvalueMInt (extract v_9865 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9873 0 1)) (uvalueMInt (extract v_9873 1 9)) (uvalueMInt (extract v_9873 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9882 0 1)) (uvalueMInt (extract v_9882 1 9)) (uvalueMInt (extract v_9882 9 32)))) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9893 0 1)) (uvalueMInt (extract v_9893 1 9)) (uvalueMInt (extract v_9893 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9901 0 1)) (uvalueMInt (extract v_9901 1 9)) (uvalueMInt (extract v_9901 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9910 0 1)) (uvalueMInt (extract v_9910 1 9)) (uvalueMInt (extract v_9910 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9920 0 1)) (uvalueMInt (extract v_9920 1 9)) (uvalueMInt (extract v_9920 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9928 0 1)) (uvalueMInt (extract v_9928 1 9)) (uvalueMInt (extract v_9928 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9937 0 1)) (uvalueMInt (extract v_9937 1 9)) (uvalueMInt (extract v_9937 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9948 0 1)) (uvalueMInt (extract v_9948 1 9)) (uvalueMInt (extract v_9948 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9956 0 1)) (uvalueMInt (extract v_9956 1 9)) (uvalueMInt (extract v_9956 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9965 0 1)) (uvalueMInt (extract v_9965 1 9)) (uvalueMInt (extract v_9965 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9975 0 1)) (uvalueMInt (extract v_9975 1 9)) (uvalueMInt (extract v_9975 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9983 0 1)) (uvalueMInt (extract v_9983 1 9)) (uvalueMInt (extract v_9983 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9992 0 1)) (uvalueMInt (extract v_9992 1 9)) (uvalueMInt (extract v_9992 9 32)))) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3022 : Mem) (v_3020 : reg (bv 128)) (v_3021 : reg (bv 128)) => do
      v_20381 <- getRegister v_3020;
      v_20382 <- eval (extract v_20381 0 32);
      v_20390 <- getRegister v_3021;
      v_20391 <- eval (extract v_20390 0 32);
      v_20400 <- evaluateAddress v_3022;
      v_20401 <- load v_20400 16;
      v_20402 <- eval (extract v_20401 0 32);
      v_20412 <- eval (extract v_20381 32 64);
      v_20420 <- eval (extract v_20390 32 64);
      v_20429 <- eval (extract v_20401 32 64);
      v_20440 <- eval (extract v_20381 64 96);
      v_20448 <- eval (extract v_20390 64 96);
      v_20457 <- eval (extract v_20401 64 96);
      v_20467 <- eval (extract v_20381 96 128);
      v_20475 <- eval (extract v_20390 96 128);
      v_20484 <- eval (extract v_20401 96 128);
      setRegister (lhs.of_reg v_3021) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20382 0 1)) (uvalueMInt (extract v_20382 1 9)) (uvalueMInt (extract v_20382 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20391 0 1)) (uvalueMInt (extract v_20391 1 9)) (uvalueMInt (extract v_20391 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20402 0 1)) (uvalueMInt (extract v_20402 1 9)) (uvalueMInt (extract v_20402 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20412 0 1)) (uvalueMInt (extract v_20412 1 9)) (uvalueMInt (extract v_20412 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20420 0 1)) (uvalueMInt (extract v_20420 1 9)) (uvalueMInt (extract v_20420 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20429 0 1)) (uvalueMInt (extract v_20429 1 9)) (uvalueMInt (extract v_20429 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20440 0 1)) (uvalueMInt (extract v_20440 1 9)) (uvalueMInt (extract v_20440 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20448 0 1)) (uvalueMInt (extract v_20448 1 9)) (uvalueMInt (extract v_20448 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20457 0 1)) (uvalueMInt (extract v_20457 1 9)) (uvalueMInt (extract v_20457 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20467 0 1)) (uvalueMInt (extract v_20467 1 9)) (uvalueMInt (extract v_20467 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20475 0 1)) (uvalueMInt (extract v_20475 1 9)) (uvalueMInt (extract v_20475 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20484 0 1)) (uvalueMInt (extract v_20484 1 9)) (uvalueMInt (extract v_20484 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_3031 : Mem) (v_3032 : reg (bv 256)) (v_3033 : reg (bv 256)) => do
      v_20497 <- getRegister v_3032;
      v_20498 <- eval (extract v_20497 0 32);
      v_20506 <- getRegister v_3033;
      v_20507 <- eval (extract v_20506 0 32);
      v_20516 <- evaluateAddress v_3031;
      v_20517 <- load v_20516 32;
      v_20518 <- eval (extract v_20517 0 32);
      v_20528 <- eval (extract v_20497 32 64);
      v_20536 <- eval (extract v_20506 32 64);
      v_20545 <- eval (extract v_20517 32 64);
      v_20556 <- eval (extract v_20497 64 96);
      v_20564 <- eval (extract v_20506 64 96);
      v_20573 <- eval (extract v_20517 64 96);
      v_20583 <- eval (extract v_20497 96 128);
      v_20591 <- eval (extract v_20506 96 128);
      v_20600 <- eval (extract v_20517 96 128);
      v_20611 <- eval (extract v_20497 128 160);
      v_20619 <- eval (extract v_20506 128 160);
      v_20628 <- eval (extract v_20517 128 160);
      v_20638 <- eval (extract v_20497 160 192);
      v_20646 <- eval (extract v_20506 160 192);
      v_20655 <- eval (extract v_20517 160 192);
      v_20666 <- eval (extract v_20497 192 224);
      v_20674 <- eval (extract v_20506 192 224);
      v_20683 <- eval (extract v_20517 192 224);
      v_20693 <- eval (extract v_20497 224 256);
      v_20701 <- eval (extract v_20506 224 256);
      v_20710 <- eval (extract v_20517 224 256);
      setRegister (lhs.of_reg v_3033) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20498 0 1)) (uvalueMInt (extract v_20498 1 9)) (uvalueMInt (extract v_20498 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20507 0 1)) (uvalueMInt (extract v_20507 1 9)) (uvalueMInt (extract v_20507 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20518 0 1)) (uvalueMInt (extract v_20518 1 9)) (uvalueMInt (extract v_20518 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20528 0 1)) (uvalueMInt (extract v_20528 1 9)) (uvalueMInt (extract v_20528 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20536 0 1)) (uvalueMInt (extract v_20536 1 9)) (uvalueMInt (extract v_20536 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20545 0 1)) (uvalueMInt (extract v_20545 1 9)) (uvalueMInt (extract v_20545 9 32)))) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20556 0 1)) (uvalueMInt (extract v_20556 1 9)) (uvalueMInt (extract v_20556 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20564 0 1)) (uvalueMInt (extract v_20564 1 9)) (uvalueMInt (extract v_20564 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20573 0 1)) (uvalueMInt (extract v_20573 1 9)) (uvalueMInt (extract v_20573 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20583 0 1)) (uvalueMInt (extract v_20583 1 9)) (uvalueMInt (extract v_20583 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20591 0 1)) (uvalueMInt (extract v_20591 1 9)) (uvalueMInt (extract v_20591 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20600 0 1)) (uvalueMInt (extract v_20600 1 9)) (uvalueMInt (extract v_20600 9 32)))) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20611 0 1)) (uvalueMInt (extract v_20611 1 9)) (uvalueMInt (extract v_20611 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20619 0 1)) (uvalueMInt (extract v_20619 1 9)) (uvalueMInt (extract v_20619 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20628 0 1)) (uvalueMInt (extract v_20628 1 9)) (uvalueMInt (extract v_20628 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20638 0 1)) (uvalueMInt (extract v_20638 1 9)) (uvalueMInt (extract v_20638 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20646 0 1)) (uvalueMInt (extract v_20646 1 9)) (uvalueMInt (extract v_20646 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20655 0 1)) (uvalueMInt (extract v_20655 1 9)) (uvalueMInt (extract v_20655 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20666 0 1)) (uvalueMInt (extract v_20666 1 9)) (uvalueMInt (extract v_20666 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20674 0 1)) (uvalueMInt (extract v_20674 1 9)) (uvalueMInt (extract v_20674 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20683 0 1)) (uvalueMInt (extract v_20683 1 9)) (uvalueMInt (extract v_20683 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20693 0 1)) (uvalueMInt (extract v_20693 1 9)) (uvalueMInt (extract v_20693 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20701 0 1)) (uvalueMInt (extract v_20701 1 9)) (uvalueMInt (extract v_20701 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20710 0 1)) (uvalueMInt (extract v_20710 1 9)) (uvalueMInt (extract v_20710 9 32)))) 32)))));
      pure ()
    pat_end
