def pminsb1 : instruction :=
  definst "pminsb" $ do
    pattern fun (v_2602 : reg (bv 128)) (v_2603 : reg (bv 128)) => do
      v_5084 <- getRegister v_2603;
      v_5085 <- eval (extract v_5084 0 8);
      v_5086 <- getRegister v_2602;
      v_5087 <- eval (extract v_5086 0 8);
      v_5090 <- eval (extract v_5084 8 16);
      v_5091 <- eval (extract v_5086 8 16);
      v_5094 <- eval (extract v_5084 16 24);
      v_5095 <- eval (extract v_5086 16 24);
      v_5098 <- eval (extract v_5084 24 32);
      v_5099 <- eval (extract v_5086 24 32);
      v_5102 <- eval (extract v_5084 32 40);
      v_5103 <- eval (extract v_5086 32 40);
      v_5106 <- eval (extract v_5084 40 48);
      v_5107 <- eval (extract v_5086 40 48);
      v_5110 <- eval (extract v_5084 48 56);
      v_5111 <- eval (extract v_5086 48 56);
      v_5114 <- eval (extract v_5084 56 64);
      v_5115 <- eval (extract v_5086 56 64);
      v_5118 <- eval (extract v_5084 64 72);
      v_5119 <- eval (extract v_5086 64 72);
      v_5122 <- eval (extract v_5084 72 80);
      v_5123 <- eval (extract v_5086 72 80);
      v_5126 <- eval (extract v_5084 80 88);
      v_5127 <- eval (extract v_5086 80 88);
      v_5130 <- eval (extract v_5084 88 96);
      v_5131 <- eval (extract v_5086 88 96);
      v_5134 <- eval (extract v_5084 96 104);
      v_5135 <- eval (extract v_5086 96 104);
      v_5138 <- eval (extract v_5084 104 112);
      v_5139 <- eval (extract v_5086 104 112);
      v_5142 <- eval (extract v_5084 112 120);
      v_5143 <- eval (extract v_5086 112 120);
      v_5146 <- eval (extract v_5084 120 128);
      v_5147 <- eval (extract v_5086 120 128);
      setRegister (lhs.of_reg v_2603) (concat (mux (slt v_5085 v_5087) v_5085 v_5087) (concat (mux (slt v_5090 v_5091) v_5090 v_5091) (concat (mux (slt v_5094 v_5095) v_5094 v_5095) (concat (mux (slt v_5098 v_5099) v_5098 v_5099) (concat (mux (slt v_5102 v_5103) v_5102 v_5103) (concat (mux (slt v_5106 v_5107) v_5106 v_5107) (concat (mux (slt v_5110 v_5111) v_5110 v_5111) (concat (mux (slt v_5114 v_5115) v_5114 v_5115) (concat (mux (slt v_5118 v_5119) v_5118 v_5119) (concat (mux (slt v_5122 v_5123) v_5122 v_5123) (concat (mux (slt v_5126 v_5127) v_5126 v_5127) (concat (mux (slt v_5130 v_5131) v_5130 v_5131) (concat (mux (slt v_5134 v_5135) v_5134 v_5135) (concat (mux (slt v_5138 v_5139) v_5138 v_5139) (concat (mux (slt v_5142 v_5143) v_5142 v_5143) (mux (slt v_5146 v_5147) v_5146 v_5147))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2597 : Mem) (v_2598 : reg (bv 128)) => do
      v_12469 <- getRegister v_2598;
      v_12470 <- eval (extract v_12469 0 8);
      v_12471 <- evaluateAddress v_2597;
      v_12472 <- load v_12471 16;
      v_12473 <- eval (extract v_12472 0 8);
      v_12476 <- eval (extract v_12469 8 16);
      v_12477 <- eval (extract v_12472 8 16);
      v_12480 <- eval (extract v_12469 16 24);
      v_12481 <- eval (extract v_12472 16 24);
      v_12484 <- eval (extract v_12469 24 32);
      v_12485 <- eval (extract v_12472 24 32);
      v_12488 <- eval (extract v_12469 32 40);
      v_12489 <- eval (extract v_12472 32 40);
      v_12492 <- eval (extract v_12469 40 48);
      v_12493 <- eval (extract v_12472 40 48);
      v_12496 <- eval (extract v_12469 48 56);
      v_12497 <- eval (extract v_12472 48 56);
      v_12500 <- eval (extract v_12469 56 64);
      v_12501 <- eval (extract v_12472 56 64);
      v_12504 <- eval (extract v_12469 64 72);
      v_12505 <- eval (extract v_12472 64 72);
      v_12508 <- eval (extract v_12469 72 80);
      v_12509 <- eval (extract v_12472 72 80);
      v_12512 <- eval (extract v_12469 80 88);
      v_12513 <- eval (extract v_12472 80 88);
      v_12516 <- eval (extract v_12469 88 96);
      v_12517 <- eval (extract v_12472 88 96);
      v_12520 <- eval (extract v_12469 96 104);
      v_12521 <- eval (extract v_12472 96 104);
      v_12524 <- eval (extract v_12469 104 112);
      v_12525 <- eval (extract v_12472 104 112);
      v_12528 <- eval (extract v_12469 112 120);
      v_12529 <- eval (extract v_12472 112 120);
      v_12532 <- eval (extract v_12469 120 128);
      v_12533 <- eval (extract v_12472 120 128);
      setRegister (lhs.of_reg v_2598) (concat (mux (slt v_12470 v_12473) v_12470 v_12473) (concat (mux (slt v_12476 v_12477) v_12476 v_12477) (concat (mux (slt v_12480 v_12481) v_12480 v_12481) (concat (mux (slt v_12484 v_12485) v_12484 v_12485) (concat (mux (slt v_12488 v_12489) v_12488 v_12489) (concat (mux (slt v_12492 v_12493) v_12492 v_12493) (concat (mux (slt v_12496 v_12497) v_12496 v_12497) (concat (mux (slt v_12500 v_12501) v_12500 v_12501) (concat (mux (slt v_12504 v_12505) v_12504 v_12505) (concat (mux (slt v_12508 v_12509) v_12508 v_12509) (concat (mux (slt v_12512 v_12513) v_12512 v_12513) (concat (mux (slt v_12516 v_12517) v_12516 v_12517) (concat (mux (slt v_12520 v_12521) v_12520 v_12521) (concat (mux (slt v_12524 v_12525) v_12524 v_12525) (concat (mux (slt v_12528 v_12529) v_12528 v_12529) (mux (slt v_12532 v_12533) v_12532 v_12533))))))))))))))));
      pure ()
    pat_end
