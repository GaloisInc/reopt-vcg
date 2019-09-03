def vfnmsub231ps1 : instruction :=
  definst "vfnmsub231ps" $ do
    pattern fun (v_3443 : reg (bv 128)) (v_3444 : reg (bv 128)) (v_3445 : reg (bv 128)) => do
      v_12487 <- getRegister v_3444;
      v_12488 <- eval (extract v_12487 0 32);
      v_12496 <- getRegister v_3443;
      v_12497 <- eval (extract v_12496 0 32);
      v_12507 <- getRegister v_3445;
      v_12508 <- eval (extract v_12507 0 32);
      v_12518 <- eval (extract v_12487 32 64);
      v_12526 <- eval (extract v_12496 32 64);
      v_12536 <- eval (extract v_12507 32 64);
      v_12546 <- eval (extract v_12487 64 96);
      v_12554 <- eval (extract v_12496 64 96);
      v_12564 <- eval (extract v_12507 64 96);
      v_12574 <- eval (extract v_12487 96 128);
      v_12582 <- eval (extract v_12496 96 128);
      v_12592 <- eval (extract v_12507 96 128);
      setRegister (lhs.of_reg v_3445) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12488 0 1)) (uvalueMInt (extract v_12488 1 9)) (uvalueMInt (extract v_12488 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12497 0 1)) (uvalueMInt (extract v_12497 1 9)) (uvalueMInt (extract v_12497 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12508 0 1)) (uvalueMInt (extract v_12508 1 9)) (uvalueMInt (extract v_12508 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12518 0 1)) (uvalueMInt (extract v_12518 1 9)) (uvalueMInt (extract v_12518 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12526 0 1)) (uvalueMInt (extract v_12526 1 9)) (uvalueMInt (extract v_12526 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12536 0 1)) (uvalueMInt (extract v_12536 1 9)) (uvalueMInt (extract v_12536 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12546 0 1)) (uvalueMInt (extract v_12546 1 9)) (uvalueMInt (extract v_12546 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12554 0 1)) (uvalueMInt (extract v_12554 1 9)) (uvalueMInt (extract v_12554 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12564 0 1)) (uvalueMInt (extract v_12564 1 9)) (uvalueMInt (extract v_12564 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12574 0 1)) (uvalueMInt (extract v_12574 1 9)) (uvalueMInt (extract v_12574 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12582 0 1)) (uvalueMInt (extract v_12582 1 9)) (uvalueMInt (extract v_12582 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12592 0 1)) (uvalueMInt (extract v_12592 1 9)) (uvalueMInt (extract v_12592 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_3454 : reg (bv 256)) (v_3455 : reg (bv 256)) (v_3456 : reg (bv 256)) => do
      v_12611 <- getRegister v_3455;
      v_12612 <- eval (extract v_12611 0 32);
      v_12620 <- getRegister v_3454;
      v_12621 <- eval (extract v_12620 0 32);
      v_12631 <- getRegister v_3456;
      v_12632 <- eval (extract v_12631 0 32);
      v_12642 <- eval (extract v_12611 32 64);
      v_12650 <- eval (extract v_12620 32 64);
      v_12660 <- eval (extract v_12631 32 64);
      v_12670 <- eval (extract v_12611 64 96);
      v_12678 <- eval (extract v_12620 64 96);
      v_12688 <- eval (extract v_12631 64 96);
      v_12698 <- eval (extract v_12611 96 128);
      v_12706 <- eval (extract v_12620 96 128);
      v_12716 <- eval (extract v_12631 96 128);
      v_12729 <- eval (extract v_12611 128 160);
      v_12737 <- eval (extract v_12620 128 160);
      v_12747 <- eval (extract v_12631 128 160);
      v_12757 <- eval (extract v_12611 160 192);
      v_12765 <- eval (extract v_12620 160 192);
      v_12775 <- eval (extract v_12631 160 192);
      v_12785 <- eval (extract v_12611 192 224);
      v_12793 <- eval (extract v_12620 192 224);
      v_12803 <- eval (extract v_12631 192 224);
      v_12813 <- eval (extract v_12611 224 256);
      v_12821 <- eval (extract v_12620 224 256);
      v_12831 <- eval (extract v_12631 224 256);
      setRegister (lhs.of_reg v_3456) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12612 0 1)) (uvalueMInt (extract v_12612 1 9)) (uvalueMInt (extract v_12612 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12621 0 1)) (uvalueMInt (extract v_12621 1 9)) (uvalueMInt (extract v_12621 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12632 0 1)) (uvalueMInt (extract v_12632 1 9)) (uvalueMInt (extract v_12632 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12642 0 1)) (uvalueMInt (extract v_12642 1 9)) (uvalueMInt (extract v_12642 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12650 0 1)) (uvalueMInt (extract v_12650 1 9)) (uvalueMInt (extract v_12650 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12660 0 1)) (uvalueMInt (extract v_12660 1 9)) (uvalueMInt (extract v_12660 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12670 0 1)) (uvalueMInt (extract v_12670 1 9)) (uvalueMInt (extract v_12670 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12678 0 1)) (uvalueMInt (extract v_12678 1 9)) (uvalueMInt (extract v_12678 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12688 0 1)) (uvalueMInt (extract v_12688 1 9)) (uvalueMInt (extract v_12688 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12698 0 1)) (uvalueMInt (extract v_12698 1 9)) (uvalueMInt (extract v_12698 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12706 0 1)) (uvalueMInt (extract v_12706 1 9)) (uvalueMInt (extract v_12706 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12716 0 1)) (uvalueMInt (extract v_12716 1 9)) (uvalueMInt (extract v_12716 9 32)))) 32)))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12729 0 1)) (uvalueMInt (extract v_12729 1 9)) (uvalueMInt (extract v_12729 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12737 0 1)) (uvalueMInt (extract v_12737 1 9)) (uvalueMInt (extract v_12737 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12747 0 1)) (uvalueMInt (extract v_12747 1 9)) (uvalueMInt (extract v_12747 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12757 0 1)) (uvalueMInt (extract v_12757 1 9)) (uvalueMInt (extract v_12757 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12765 0 1)) (uvalueMInt (extract v_12765 1 9)) (uvalueMInt (extract v_12765 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12775 0 1)) (uvalueMInt (extract v_12775 1 9)) (uvalueMInt (extract v_12775 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12785 0 1)) (uvalueMInt (extract v_12785 1 9)) (uvalueMInt (extract v_12785 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12793 0 1)) (uvalueMInt (extract v_12793 1 9)) (uvalueMInt (extract v_12793 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12803 0 1)) (uvalueMInt (extract v_12803 1 9)) (uvalueMInt (extract v_12803 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12813 0 1)) (uvalueMInt (extract v_12813 1 9)) (uvalueMInt (extract v_12813 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12821 0 1)) (uvalueMInt (extract v_12821 1 9)) (uvalueMInt (extract v_12821 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12831 0 1)) (uvalueMInt (extract v_12831 1 9)) (uvalueMInt (extract v_12831 9 32)))) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3440 : Mem) (v_3438 : reg (bv 128)) (v_3439 : reg (bv 128)) => do
      v_23046 <- getRegister v_3438;
      v_23047 <- eval (extract v_23046 0 32);
      v_23055 <- evaluateAddress v_3440;
      v_23056 <- load v_23055 16;
      v_23057 <- eval (extract v_23056 0 32);
      v_23067 <- getRegister v_3439;
      v_23068 <- eval (extract v_23067 0 32);
      v_23078 <- eval (extract v_23046 32 64);
      v_23086 <- eval (extract v_23056 32 64);
      v_23096 <- eval (extract v_23067 32 64);
      v_23106 <- eval (extract v_23046 64 96);
      v_23114 <- eval (extract v_23056 64 96);
      v_23124 <- eval (extract v_23067 64 96);
      v_23134 <- eval (extract v_23046 96 128);
      v_23142 <- eval (extract v_23056 96 128);
      v_23152 <- eval (extract v_23067 96 128);
      setRegister (lhs.of_reg v_3439) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23047 0 1)) (uvalueMInt (extract v_23047 1 9)) (uvalueMInt (extract v_23047 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23057 0 1)) (uvalueMInt (extract v_23057 1 9)) (uvalueMInt (extract v_23057 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23068 0 1)) (uvalueMInt (extract v_23068 1 9)) (uvalueMInt (extract v_23068 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23078 0 1)) (uvalueMInt (extract v_23078 1 9)) (uvalueMInt (extract v_23078 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23086 0 1)) (uvalueMInt (extract v_23086 1 9)) (uvalueMInt (extract v_23086 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23096 0 1)) (uvalueMInt (extract v_23096 1 9)) (uvalueMInt (extract v_23096 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23106 0 1)) (uvalueMInt (extract v_23106 1 9)) (uvalueMInt (extract v_23106 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23114 0 1)) (uvalueMInt (extract v_23114 1 9)) (uvalueMInt (extract v_23114 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23124 0 1)) (uvalueMInt (extract v_23124 1 9)) (uvalueMInt (extract v_23124 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23134 0 1)) (uvalueMInt (extract v_23134 1 9)) (uvalueMInt (extract v_23134 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23142 0 1)) (uvalueMInt (extract v_23142 1 9)) (uvalueMInt (extract v_23142 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23152 0 1)) (uvalueMInt (extract v_23152 1 9)) (uvalueMInt (extract v_23152 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_3449 : Mem) (v_3450 : reg (bv 256)) (v_3451 : reg (bv 256)) => do
      v_23166 <- getRegister v_3450;
      v_23167 <- eval (extract v_23166 0 32);
      v_23175 <- evaluateAddress v_3449;
      v_23176 <- load v_23175 32;
      v_23177 <- eval (extract v_23176 0 32);
      v_23187 <- getRegister v_3451;
      v_23188 <- eval (extract v_23187 0 32);
      v_23198 <- eval (extract v_23166 32 64);
      v_23206 <- eval (extract v_23176 32 64);
      v_23216 <- eval (extract v_23187 32 64);
      v_23226 <- eval (extract v_23166 64 96);
      v_23234 <- eval (extract v_23176 64 96);
      v_23244 <- eval (extract v_23187 64 96);
      v_23254 <- eval (extract v_23166 96 128);
      v_23262 <- eval (extract v_23176 96 128);
      v_23272 <- eval (extract v_23187 96 128);
      v_23285 <- eval (extract v_23166 128 160);
      v_23293 <- eval (extract v_23176 128 160);
      v_23303 <- eval (extract v_23187 128 160);
      v_23313 <- eval (extract v_23166 160 192);
      v_23321 <- eval (extract v_23176 160 192);
      v_23331 <- eval (extract v_23187 160 192);
      v_23341 <- eval (extract v_23166 192 224);
      v_23349 <- eval (extract v_23176 192 224);
      v_23359 <- eval (extract v_23187 192 224);
      v_23369 <- eval (extract v_23166 224 256);
      v_23377 <- eval (extract v_23176 224 256);
      v_23387 <- eval (extract v_23187 224 256);
      setRegister (lhs.of_reg v_3451) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23167 0 1)) (uvalueMInt (extract v_23167 1 9)) (uvalueMInt (extract v_23167 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23177 0 1)) (uvalueMInt (extract v_23177 1 9)) (uvalueMInt (extract v_23177 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23188 0 1)) (uvalueMInt (extract v_23188 1 9)) (uvalueMInt (extract v_23188 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23198 0 1)) (uvalueMInt (extract v_23198 1 9)) (uvalueMInt (extract v_23198 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23206 0 1)) (uvalueMInt (extract v_23206 1 9)) (uvalueMInt (extract v_23206 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23216 0 1)) (uvalueMInt (extract v_23216 1 9)) (uvalueMInt (extract v_23216 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23226 0 1)) (uvalueMInt (extract v_23226 1 9)) (uvalueMInt (extract v_23226 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23234 0 1)) (uvalueMInt (extract v_23234 1 9)) (uvalueMInt (extract v_23234 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23244 0 1)) (uvalueMInt (extract v_23244 1 9)) (uvalueMInt (extract v_23244 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23254 0 1)) (uvalueMInt (extract v_23254 1 9)) (uvalueMInt (extract v_23254 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23262 0 1)) (uvalueMInt (extract v_23262 1 9)) (uvalueMInt (extract v_23262 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23272 0 1)) (uvalueMInt (extract v_23272 1 9)) (uvalueMInt (extract v_23272 9 32)))) 32)))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23285 0 1)) (uvalueMInt (extract v_23285 1 9)) (uvalueMInt (extract v_23285 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23293 0 1)) (uvalueMInt (extract v_23293 1 9)) (uvalueMInt (extract v_23293 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23303 0 1)) (uvalueMInt (extract v_23303 1 9)) (uvalueMInt (extract v_23303 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23313 0 1)) (uvalueMInt (extract v_23313 1 9)) (uvalueMInt (extract v_23313 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23321 0 1)) (uvalueMInt (extract v_23321 1 9)) (uvalueMInt (extract v_23321 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23331 0 1)) (uvalueMInt (extract v_23331 1 9)) (uvalueMInt (extract v_23331 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23341 0 1)) (uvalueMInt (extract v_23341 1 9)) (uvalueMInt (extract v_23341 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23349 0 1)) (uvalueMInt (extract v_23349 1 9)) (uvalueMInt (extract v_23349 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23359 0 1)) (uvalueMInt (extract v_23359 1 9)) (uvalueMInt (extract v_23359 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23369 0 1)) (uvalueMInt (extract v_23369 1 9)) (uvalueMInt (extract v_23369 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23377 0 1)) (uvalueMInt (extract v_23377 1 9)) (uvalueMInt (extract v_23377 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_23387 0 1)) (uvalueMInt (extract v_23387 1 9)) (uvalueMInt (extract v_23387 9 32)))) 32)))));
      pure ()
    pat_end
